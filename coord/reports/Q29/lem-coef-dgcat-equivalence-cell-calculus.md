## Worker report

The module `Sheaf.CategoryTheory.DgCategoryEquivalenceCellCalculus` states the coherent homotopy-equivalence cell calculus over the recorded free-cell dg-category dependency. `IsH0Iso` renders an invertible degree-zero closed arrow by a closed degree-zero inverse and degree-minus-one homotopies with the two displayed differential equations. `DegreewiseSurjective` renders surjectivity of every homogeneous map on every morphism complex. `IsCellPushout` renders the selected-object pushout universal property.

`EquivalenceCellCalculus` records the dg category `K`, its two labelled objects, generators `f,g,r₀,r₁,t`, their degrees, and the four differential identities. The `realize` field states clause (a), including closedness, `H⁰` invertibility, object images, and the image of `f`. The `pushout` field states clause (b): the pushout universal property, quasi-isomorphisms on every old-object morphism complex, the old-or-single-new-object condition, and the induced `H⁰` isomorphism. The `lift` field states clause (c): degreewise surjectivity, the prescribed bottom functor and image conditions, simultaneous lifting with all object and generator equalities, and equality of the lifted square. Since the data of `K` and its generators are carried by a structure, the theorem is stated as `Nonempty (EquivalenceCellCalculus R)`.

The dependency declaration used is `CategoryTheory.Dg.FreeCellCalculus` and its supporting declarations from `Sheaf.CategoryTheory.DgCategoryFreeCellCalculus`.

Edge cases checked include `s=t` in the dg-category object variables, zero and negative generator degrees, arbitrary integer complex degree, the zero ring permitted by `CommRing`, and empty old-object families in the pushout object coverage. The module compiles cleanly with `scompile.py`; the only expected postponed proof is the theorem `sorry`.

Searches recorded on the node found no exact Mathlib or project declaration for a coherent free dg-category equivalence cell, its pushout invariance, or its lifting property (LeanFinder/LeanSearch semantic searches, Loogle, and focused grep over Mathlib and the project).

## Earlier second reading (a previous round; superseded)

I reread the node and the complete declaration in
`Sheaf.CategoryTheory.DgCategoryEquivalenceCellCalculus`. The structure field `K`,
the `ULift (Fin 2)` equivalence, and the six generator fields render exactly the
free two-object dg category and the displayed degrees. The fields `df`, `dg`,
`dr₀`, `dr₁`, and `dt` reproduce all four differential identities, with
`mulAt`/`mulAtDegree` expressing the stated right-to-left compositions. The
`realize` field has the closedness and `IsH0Iso` hypotheses and returns a functor
with both object images and the prescribed image of `f`, matching (a). The
`pushout` field states the selected-object pushout universal property, old-object
`QuasiIso` maps, the old-or-new object coverage, and the induced `H⁰` isomorphism,
matching (b). The `lift` field states degreewise surjectivity, the fixed source
object, the bottom functor's object and `f` images, and a filler with all object,
`f`, and square equalities, matching (c). No hypothesis or conclusion is added,
dropped, strengthened, or weakened. The only proof is the required `sorry` in
`equivalenceCellCalculus`; all structure data are explicit.

## Second reading by Q29

I opened the node, its source place, the dependency node and declaration, and the
sandbox module. The node introduces a commutative ring `R`; the free two-object
`R`-linear cochain dg category `K_R`; objects `0,1`; arrows `f : 0 → 1` and
`g : 1 → 0` in degree `0`; arrows `r₀,r₁` in degree `-1`; and `t : 0 → 1`
in degree `-2`, with right-to-left composition and the four displayed
 differential identities. The module renders these as `R : Type u` with
`[CommRing R]`, `K : Cat R`, `obj : ULift (Fin 2) ≃ K`, the five homogeneous
fields, and `df`, `dg`, `dr₀`, `dr₁`, `dt`; `mulAt` and `mulAtDegree` preserve the
specified degree casts and composition order. The zero ring, characteristic two,
negative degrees, and coincident labelled objects are all permitted.

The phrase “free” is rendered by the added `IsFreeCell` field. It gives, for every
`B`, two target objects and five target homogeneous arrows satisfying exactly the
same four differential equations, a unique dg functor `K ⟶ B` with both object
images and all five generator images prescribed. This is the universal presentation
of the source's free dg category and fixes the previous omission of that property.

For (a), `realize` quantifies over every `B`, objects `x,y`, and closed degree-zero
`u`; `IsH0Iso` expands to a closed degree-zero inverse and the two degree-minus-one
homotopies with the node's equations, and the conclusion gives a dg functor with
both object images and `f` sent to `u` (the dependent equality is expressed by
`HEq`). No extra finiteness, characteristic, or invertibility hypothesis appears.

For (b), `pushout` quantifies over every `C` and `c`, and supplies `E`, `jC`, and
`jK`. `IsCellPushout` gives the selected-object equality and the full strict
universal property; the next conjunct gives quasi-isomorphisms on every old pair;
the object coverage says every object is an old image or exactly the new image of
`1`; and `IsH0Iso` on the image of `f` gives the induced `H⁰` isomorphism. Empty
old-object families and the zero category remain covered by these universal
quantifiers.

For (c), `DegreewiseSurjective` is surjectivity of every homogeneous map of every
morphism complex. The corrected `lift` now states the square's object equations
`q.obj 0 = p.obj x` and `q.obj 1 = p.obj x'`, together with the prescribed image of
`f`; it concludes a filler with both object images, `f` sent to `u`, and strict
square equality `q = F ≫ p`. This matches the source's lifting square, including
its fixed top object and the specified target image. The arbitrary integer degree
parameter and all zero/negative cases are retained.

The first reading found two mismatches. First, the structure had no field asserting
that `K` was free, so it could describe an arbitrary two-object dg category with
five arrows and the relations; I added the documented `IsFreeCell` universal
presentation and recorded it in the node's `lean.declarations`. Second, the lift
hypothesis incorrectly required `q.obj 0 = p.obj x'` and omitted the equation at
object `1`; I replaced it by `q.obj 0 = p.obj x` and added `q.obj 1 = p.obj x'`.
No node TeX statement, dependency list, or proof field was changed.

I searched the dependency and source trees and Mathlib with focused `rg` searches
for `EquivalenceCellCalculus`, `IsFreeCell`, `dg interval`, `Kontsevich`,
`quasi-equivalence`, and the generator names, and ran LeanFinder, LeanSearch, and
Loogle searches recorded on the node. There is no existing declaration of this
free-cell presentation or of the realization/pushout/lifting statement. The source
PDF at Tabuada, arXiv:0710.4303, Chapter 1 §1.3.1, printed pp. 27--32, confirms
both the free presentation and the lifting object assignments. The repaired module
compiled cleanly with `scompile.py`; only the theorem's expected `sorry` remains.
