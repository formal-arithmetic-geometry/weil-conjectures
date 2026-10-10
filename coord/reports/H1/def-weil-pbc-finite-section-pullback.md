# Stage 1 attachment: `def-weil-pbc-finite-section-pullback`

## Worker report

Exact source declaration: `AlgebraicGeometry.Etale.globalSectionsUpperStarMap` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/SixFunctors/Etale/UpperLowerStar/GlobalSections.lean:57-64` belongs to `def-weil-pbc-finite-section-pullback`. Its docstring at line 56 names this blueprint node. It constructs `Γ(Y,G) ⟶ Γ(X,f^*G)` by evaluating the adjunction unit `G ⟶ f_*f^*G` at the terminal object and transporting through the global-section/terminal-section isomorphisms. It is defined for every scheme morphism `f`, and therefore specializes to finite `h:V ⟶ Y`. The body contains no `sorry`.

The accompanying `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/SixFunctors/BaseChange/GlobalSections.lean:15-16` calls this map `h^♯` and confirms that finiteness plays no role. The node itself has no Lean attachment in its audit. Per the brief, no DAG split or new node was written; the lead should verify the compiled sorry map and attach this declaration, marking the item closed if its transitive dependencies are sorry-free.

No WANTED source or statement change. The blueprint node describes the map on a section of an étale sheaf; the Lean definition packages the same operation as a morphism between global-section objects in an abelian category. The lead should check this representation against the intended coefficient category before attaching.

## Review by H1

I verified the exact blueprint marker and definition in `WeilConjectures/SixFunctors/Etale/UpperLowerStar/GlobalSections.lean:56-64`. `AlgebraicGeometry.Etale.globalSectionsUpperStarMap` constructs the adjunction-unit map between global sections; the BaseChange wrapper identifies it as finite-section pullback $h^\sharp$. The local sorry map reports the definition and all transitive dependencies sorry-free. This node is closed on slopmaster2; no split is needed.
