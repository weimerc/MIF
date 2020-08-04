extensions [ nw ]

globals [ MC-list clusters cluster-ops ]

turtles-own [ opinion next-opinion ]

;;;;; SETUP ;;;;;

to setup
  clear-all
  setup-turtles
  reset-ticks
  setup-plot
  set search-delta min list search-delta (1 / round (2 / group-width))
end

to setup-turtles
  set-default-shape turtles "dot"
  ifelse SWN? [ ; generate small-world network using Watts-Strogatz method
    nw:generate-watts-strogatz turtles links N num-neighbors p-rewire [
      set size 0.5
      fd min list max-pxcor max-pycor
      initialize-turtle
    ]
  ] [ ; else, don't bother with links
    create-turtles N [
      set size 0.5
      set heading (who / N) * 359
      fd min list max-pxcor max-pycor
      initialize-turtle
    ]
  ]
end

to initialize-turtle
  set opinion random-float 1
  set next-opinion opinion
  set color hsb (260 * opinion + 5) 100 100
end

to setup-plot
  set-current-plot "Opinion over time"
  ask turtles [
    create-temporary-plot-pen word "Turtle " who
    set-plot-pen-color color
;    plot-pen-up
  ]
  ask turtles [ update-plot ]
end




;;;;; GO ;;;;;

to go
  let prim-actors ifelse-value (num-prim-actors >= N) [ turtles ] [ n-of num-prim-actors turtles ]
  if (not SWN?) and synchrony = "Synchronous" [set-noSWN-source]
  ask prim-actors [
    if (not SWN?) and synchrony = "Asynchronous" [set-noSWN-source]
    be-influenced
  ]
  if synchrony = "Synchronous" [ ask prim-actors [ update-opinion ] ]
  tick
  if op-plot? [ if ticks mod update-freq = 0 [ ask turtles [ update-plot ] ] ]
  update-clusters
  let max-op max [opinion] of turtles
  let min-op min [opinion] of turtles
  if count turtles with [opinion = min-op or opinion = max-op] = N [ stop ]
  if max-op - min-op < 0.01 [ stop ]
  if not SWN? and k < 1 [ if max map [ [y] -> max [opinion] of y - min [opinion] of y ] clusters <= (group-width / 2) [stop] ]
  if not SWN? [ if length remove-duplicates [opinion] of turtles <= length MC-list [ stop ] ]
end



;;;;; PROCEDURES ;;;;;

;; OBSERVER PROCEDURES ;;

to set-noSWN-source ; pre-calculates values for fully connected values
  set MC-list []
  let ops [opinion] of turtles
  ; create list of prototypicality values
  let inputs map [ [y] -> y * search-delta ] range ((1 / search-delta) + 1)
  let x-list []
  let P-list []
  foreach inputs [ [x] ->
    set x-list lput x x-list
    set P-list lput (prototypicality x ops) P-list
  ]
  ; eliminate values that are not local maxima
  let decreasing? false
  foreach range (length x-list) [ [index] ->
    ifelse decreasing? [
      if index < length x-list - 1 [
        if (item index P-list) < (item (index + 1) P-list) [
          set decreasing? false
        ]
      ]
    ] [ ; not decreasing?
      ifelse index = length x-list - 1 [
        set MC-list lput last x-list MC-list
      ] [
        if (item index P-list) > (item (index + 1) P-list) [
          set MC-list lput (item index x-list) MC-list
          set decreasing? true
        ]
      ]
    ]
  ]
end

to update-clusters
  let old-clusters clusters
  set clusters remove-duplicates [ turtles with [abs (opinion - [opinion] of myself) < group-width] ] of turtles
  set cluster-ops map [ [y] -> mean [opinion] of y ] clusters
end

;; TURTLE PROCEDURES ;;

to update-plot
  set-current-plot "Opinion over time"
  set-current-plot-pen word "Turtle " who
  plotxy ticks opinion
end

to update-opinion
  set opinion next-opinion
  if opinion > 1 [ set opinion 1 ]
  if opinion < 0 [ set opinion 0 ]
  set color hsb (260 * opinion + 5) 100 100
end

to be-influenced
  let ops get-ops
  let influence get-influence ops
  set next-opinion next-opinion + influence
  if synchrony = "Asynchronous" [ update-opinion ]
end


;;;;; FUNCTIONS ;;;;;

;; OBSERVER FUNCTIONS ;;

to-report membership [x xi] ; mu(x,x_i) in Salzarulo (2006)
  ;; Note: this assumes agents are unaware of group membership (may not be appropriate in all cases)
  let w group-width
  report exp (- ((x - xi) ^ 2 / (w ^ 2)))
end

to-report prototypicality [ x ops ] ; P(x,X) in Salzarulo (2006)
  let a outgroup-aversion
  let w group-width
  let mus map [[xi] -> membership x xi] ops
  let diffs2 map [[y] -> (x - item y ops) ^ 2 ] range length ops
  let summus sum mus ; sum(mu(x,xi))
  let diff2mus sum map [[y] -> (item y mus) * (item y diffs2)] range length ops; sum((x-xi)^2 mu(x,xi))
  let summus2 (length ops) - summus ; sum(1-mu(x,xi))
  let diff2mus2 sum map [[y] -> (1 - item y mus) * (item y diffs2)] range length ops; sum((x-xi)^2 (1-mu(x,xi)))
  let dintra ifelse-value (summus = 0) [0] [diff2mus / summus]
  let dinter ifelse-value (summus2 = 0) [0] [diff2mus2 / summus2]
  let P (a * dinter - (1 - a) * dintra)
  report P
end

to-report influence-MC [ x ops ]
  let proto-ops []
  ifelse SWN? [
    foreach list (- search-delta) search-delta  [ [eps] -> ; find local maxima in each direction
      let proto-op x
      let P prototypicality proto-op ops
      let decreasing? true ; becomes false once first local minimum is found
      let increasing? true ; becomes false once first local maximum is found
      while [increasing? and (proto-op >= 0) and (proto-op <= 1)] [
        set proto-op (proto-op + eps)
        let Pnew prototypicality proto-op ops
        ifelse decreasing? [
          if Pnew > P [ set decreasing? false ]
        ] [ ; not decreasing
          if Pnew < P [ ; last value was the local maximum
            set increasing? false
            set proto-op (proto-op - eps)
          ]
        ]
        set P Pnew
      ]
      if not decreasing? [ set proto-ops lput proto-op proto-ops ]
    ]
    if (proto-ops = []) [set proto-ops (list x) ]
  ] [ ; fully connected model
    set proto-ops MC-list
  ]
  let proto-distance (map [ [y] -> abs (x - y) ] proto-ops)
  let my-proto-op item (position (min proto-distance) proto-distance) proto-ops
  let source-op 0
  let source-distance min map [ [y] -> abs (y - my-proto-op) ] ops
  set source-op item 0 (filter [ [y] -> abs (y - my-proto-op) = source-distance] ops)
  if source-op > 1 [ set source-op 1 ]
  if source-op < 0 [ set source-op 0 ]
  let influence k * (source-op - x)
  report influence
end

to-report check-influence
  let done? true
  ask turtles [
    if done? [
      if get-influence get-ops != 0 [ set done? false ]
    ]
  ]
  report done?
end

to-report skewness [ xlist ]
  let len length xlist
  let xbar mean xlist
  let skew (sum map [ [x] -> (x - xbar) ^ 3 ] xlist) / ( len * (((len - 1) / len) * variance xlist) ^ 1.5)
  report skew
end

to-report kurtosis [ xlist ]
  let len length xlist
  let xbar mean xlist
  let kurt (sum map [ [x] -> (x - xbar) ^ 4 ] xlist) / ( len * (((len - 1) / len) * variance xlist) ^ 2)
  report kurt
end

;; TURTLE FUNCTIONS ;;

to-report get-ops
  let ops []
  ifelse SWN? [ set ops [opinion] of (turtle-set link-neighbors self) ] [ set ops [opinion] of turtles ]
  report ops
end

to-report get-influence [ ops ]
  let influence influence-MC opinion ops
  report influence
end
@#$#@#$#@
GRAPHICS-WINDOW
425
303
748
627
-1
-1
15.0
1
10
1
1
1
0
0
0
1
-10
10
-10
10
1
1
1
ticks
30.0

TEXTBOX
9
18
87
36
Model Controls:
11
0.0
1

BUTTON
93
10
157
43
Setup
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
177
10
240
43
Step
go
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
0

BUTTON
240
10
303
43
Go
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
0

TEXTBOX
45
64
85
82
Agents:
11
0.0
1

SLIDER
93
56
235
89
N
N
100
1000
100.0
100
1
agents
HORIZONTAL

TEXTBOX
3
110
85
128
Agent Schedule:
11
0.0
1

SLIDER
190
103
333
136
num-prim-actors
num-prim-actors
1
N
1.0
1
1
= t
HORIZONTAL

TEXTBOX
35
178
80
196
Network:
11
0.0
1

SWITCH
93
170
190
203
SWN?
SWN?
0
1
-1000

SLIDER
190
154
333
187
num-neighbors
num-neighbors
1
(N / 2) - 1
8.0
1
1
agents
HORIZONTAL

SLIDER
190
187
333
220
p-rewire
p-rewire
0
1
0.05
0.01
1
NIL
HORIZONTAL

TEXTBOX
94
242
193
260
Model Parameters
11
0.0
1

SLIDER
21
294
166
327
k
k
0.01
1
1.0
0.01
1
NIL
HORIZONTAL

SLIDER
21
261
166
294
group-width
group-width
0.01
1
0.8
0.01
1
= w
HORIZONTAL

SLIDER
166
261
320
294
outgroup-aversion
outgroup-aversion
0
1
0.0
0.01
1
= a
HORIZONTAL

SLIDER
166
294
320
327
search-delta
search-delta
0.001
0.01
0.01
0.0005
1
NIL
HORIZONTAL

PLOT
345
10
899
289
Opinion over Time
time
opinion
0.0
10.0
0.0
1.0
true
false
"" ""
PENS

PLOT
14
340
387
549
Distribution of opinions
opinion
frequency
0.0
1.01
0.0
10.0
true
false
"" ""
PENS
"default" 0.0505 1 -16777216 true "" "if ticks > 0 [ histogram [opinion] of turtles ]"

SWITCH
777
289
899
322
op-plot?
op-plot?
0
1
-1000

SLIDER
777
322
899
355
update-freq
update-freq
1
100
100.0
1
1
ticks
HORIZONTAL

MONITOR
778
373
853
418
# Clusters
length clusters
0
1
11

CHOOSER
92
103
190
148
synchrony
synchrony
"Synchronous" "Asynchronous"
1

MONITOR
778
432
896
477
Clusters to remove
length remove-duplicates [opinion] of turtles - length MC-list
0
1
11

@#$#@#$#@
## WHAT IS IT?

(a general understanding of what the model is trying to show or explain)

## HOW IT WORKS

(what rules the agents use to create the overall behavior of the model)

## HOW TO USE IT

(how to use the model, including a description of each of the items in the Interface tab)

## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

(suggested things to add or change in the Code tab to make the model more complicated, detailed, accurate, etc.)

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)

## RELATED MODELS

(models in the NetLogo Models Library and elsewhere which are of related interest)

## CREDITS AND REFERENCES

(a reference to the model's URL on the web if it has one, as well as any other necessary credits, citations, and links)

Note: timer limit on BehaviorSpace is required for cases of alternating opinions (rare: 8 cases of 101000 in trial run failed to converge, and max number of ticks for those that did converge was 1614). Limit set at 5000. Salzarulo (2006) used 1500 as time limit for his simulations.
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.0
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="MC-replication" repetitions="100" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>reset-timer
setup</setup>
    <go>go</go>
    <timeLimit steps="5000"/>
    <metric>timer</metric>
    <metric>length remove-duplicates [opinion] of turtles</metric>
    <metric>remove-duplicates [opinion] of turtles</metric>
    <enumeratedValueSet variable="N">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="synchrony">
      <value value="&quot;Asynchronous&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="k">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-prim-actors">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="SWN?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-neighbors">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p-rewire">
      <value value="0.05"/>
    </enumeratedValueSet>
    <steppedValueSet variable="group-width" first="0.01" step="0.01" last="1"/>
    <steppedValueSet variable="outgroup-aversion" first="0" step="0.01" last="1"/>
    <enumeratedValueSet variable="search-delta">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op-plot?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="update-freq">
      <value value="100"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="MC-replication-SWN" repetitions="100" sequentialRunOrder="false" runMetricsEveryStep="false">
    <setup>reset-timer
setup</setup>
    <go>go</go>
    <timeLimit steps="1500"/>
    <metric>timer</metric>
    <metric>length remove-duplicates [opinion] of turtles</metric>
    <metric>remove-duplicates [opinion] of turtles</metric>
    <metric>mean [opinion] of turtles</metric>
    <metric>variance [opinion] of turtles</metric>
    <metric>skewness [opinion] of turtles</metric>
    <metric>kurtosis [opinion] of turtles</metric>
    <enumeratedValueSet variable="N">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="synchrony">
      <value value="&quot;Asynchronous&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="k">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-prim-actors">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="SWN?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-neighbors">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p-rewire">
      <value value="0"/>
      <value value="0.05"/>
      <value value="0.1"/>
    </enumeratedValueSet>
    <steppedValueSet variable="group-width" first="0.01" step="0.01" last="1"/>
    <steppedValueSet variable="outgroup-aversion" first="0" step="0.01" last="1"/>
    <enumeratedValueSet variable="search-delta">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op-plot?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="update-freq">
      <value value="100"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
0
@#$#@#$#@
