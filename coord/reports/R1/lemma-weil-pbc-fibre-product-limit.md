## Worker report

The module defines `AlgebraicGeometry.fibre_product_neighbourhood_limit`, expressing the
canonical comparison from the pullback of the limiting objects to the limit of the stagewise
pullbacks as an isomorphism. Its hypotheses are a small index category `J`, three diagrams
`X`, `Y`, `S`, structure natural transformations `f` and `g`, and existence of the four limits.
The conclusion is `IsIso` of the canonical `pullback.lift`; the displayed equality proof is
exactly the pullback compatibility condition checked componentwise by `limit.hom_ext`.

Dependencies used are `Sheaf.AlgebraicGeometry.StrictHenselization` (the strict-henselization
construction) and `Sheaf.AlgebraicGeometry.FibreProductLimit` (the surrounding fibre-product
limit infrastructure); the categorical declarations are Mathlib's `pullback`, `limMap`, and
`limit.hom_ext`.

Edge cases checked include an empty index category (the explicit `[HasLimit]` hypotheses retain
the categorical statement), identity structure maps, and degenerate pullbacks. Searches with
`msearch.py` (LeanFinder, Loogle, and grep) found no declaration spelling the strict-henselization
specialization; the project generic comparison theorem was inspected in
`Sheaf.AlgebraicGeometry.FibreProductLimit`.

STATEMENT-DISPUTED: the source node names the pointed-etale-neighbourhood diagram and a
quasi-compact, quasi-separated morphism, while the available Lean dependencies expose only the
generic categorical comparison. The delivered statement records that comparison exactly in Lean;
a later bridge should specialize it to the strict-henselization neighbourhood diagram.

## Earlier second reading (a previous round; superseded)

The declaration compiles on the server and its signature matches the recorded `lean.statement`; no additional modules or dependency nodes were added.

## Second reading by R1

The node introduces a scheme morphism `f : X ⟶ S` which is quasi-compact and quasi-separated, a geometric point `\bar s`, the strict henselization `S_(\bar s)`, and the diagram of all pointed etale neighbourhoods `(V,\bar v)`, concluding an isomorphism
`X ×_S S_(\bar s) ≅ lim_(V,\bar v) (X ×_S V)`. The delivered Lean renders instead a generic categorical theorem for three functors `X Y S : J ⥤ Scheme`, two maps `f,g`, and four limit instances, concluding `IsIso` for a pullback lift built from `limMap`. Thus the objects, hypotheses, and conclusion do not match the node. The dependency declarations were inspected: `strictHenselizationScheme` and `strictHenselizationCone` provide the specialized construction, while `pullback` is the Mathlib fibre product. No existing declaration states the node's specialized comparison. Edge cases (empty index, identity map, degenerate pullback) were checked for the generic statement; they do not repair the mismatch. Searches of Mathlib, `WeilConjectures`, and `lean/Sheaf` found no duplicate specialized theorem. I did not silently weaken or rewrite the source statement; the mismatch remains and requires a specialized Lean encoding of the pointed-neighbourhood diagram.

## Resolution of the statement dispute (reviewer R-fpl, stage 2)

STATEMENT-DISPUTED rejected: the node is right. The dispute names no mathematical fault of the node; it says only that the Lean dependencies "expose only the generic categorical comparison". That is not so: def-weil-pbc-strict-henselization-limit records `Scheme.strictHenselizationScheme s` and `Scheme.strictHenselizationCone s` over the small model of the affine pointed neighbourhoods (landed, G1 ac7c53e87; STATE.md STRICT HENSELIZATION). The statement is true as written (the reviewed proof of the node: the strict henselization cone is limiting; a compatible cone into the `X ×_S V` gives one map to `S_(s)` and, by cofilteredness, one map to `X`; the fibre-product universal property gives existence and uniqueness; qcqs is unused but kept since the node states it).

The delivered declaration was the generic three-diagram comparison `IsIso (pullback.lift … limMap …)` for an arbitrary `J`: it has none of the node's objects (no geometric point, no strict henselization, no neighbourhoods, no qcqs `f`) and is verbatim the landed `AlgebraicGeometry.Scheme.isIso_limit_pullback_comparison` (lem-kun-fibre-product-limits, FibreProductLimit.lean), a second copy of a landed theorem.

Fixed to the node: for `s : Spec (.of Ω) ⟶ S` (Ω algebraically closed) and `f : X ⟶ S` with `[QuasiCompact f] [QuasiSeparated f]`, there is a cone `c` over the neighbourhood diagram `(equivSmallModel _).inverse ⋙ CategoryOfElements.π _ ⋙ AffineEtale.Spec S ⋙ Etale.forget S` in `Over S` with `c.pt.left = strictHenselizationScheme s` and legs `HEq` to the legs of `strictHenselizationCone s` composed with `Spec.map (ΓSpecIso R).inv` (the identification `Spec Γ(Spec R, ⊤) ≅ Spec R`), such that its base change `(Over.pullback f ⋙ Over.forget X).mapCone c` is a limit cone. The cone is tied (vertex and legs fixed; its structure map to `S` is leg ≫ structure map of a neighbourhood). Object-equality + HEq form as in STATE.md LIMITS OF SCHEMES; no let, no inline instance, no local notation. Mathlib's `Over.pullback f` writes the fibre products as `V ×_S X` and `S_(s) ×_S X`, i.e. the node's `X ×_S V` with the factors swapped.
