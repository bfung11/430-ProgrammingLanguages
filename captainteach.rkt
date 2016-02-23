{class 3DPoint extends Point
  {z}
  {get-z {} z}
  {dist-from-zero {}
          {with {y = {send this get-y}}
                {with {x = {send this get-x}}
                   {with {z = {new Point 1}}}
                      {expt {+ {* z z} {+ {* y y} {* x x}}} 1/2}}}}}
