## Worker report

The module `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge` states that for schemes `X,S`, an affine morphism `h`, and a quasi-coherent module `F`, all positive right-derived direct images vanish and every natural-number edge map is an isomorphism. The binders `[IsAffineHom h]` and `[F.IsQuasicoherent]` render the two hypotheses. The two `HasDerivedCategory` binders provide the derived categories needed by the higher-direct-image expression. The first conjunct is `∀ p, 0 < p → IsZero (...)`, rendering `R^p h_* F = 0` for `p>0`; the second is `∀ p, IsIso (moduleCohomologyEdgeMap h F p)`, rendering the edge-map isomorphism for every `p≥0`. The edge map is the recorded `moduleCohomologyEdgeMap`, whose underlying additive-group morphism carries the canonical module map.

The dependency declarations used are `AlgebraicGeometry.IsAffineHom` from Mathlib `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `AlgebraicGeometry.pqfDefCoherent_quasiCoherent` from `Sheaf.AlgebraicGeometry.PqfDefCoherent`, `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` from `Sheaf.Paper.PQFCohomology`, and `AlgebraicGeometry.Scheme.Modules.moduleCohomologyEdgeMap` from `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`. The closed-immersion dependency is not used in the signature because it is only the parenthetical example in the node statement.

Edge cases checked: `p=0` is included in the edge-map clause and excluded from vanishing by `0 < p`; no nonempty or positive-index assumption is imposed; arbitrary scheme universes are retained.

Searches: `msearch.py leanfinder` for affine cohomology and `msearch.py loogle` for direct-image cohomology found no exact theorem; grep of Mathlib and `WeilConjectures` found no affine O-module cohomology edge theorem. `rg` found Mathlib's `SheafOfModules.IsQuasicoherent` and the project's `moduleCohomologyEdgeMap`.

## Dependency modules

`pqf-def-coherent` had the recorded `RingedSpace.IsCoherent`, which states the stronger coherent conjunction and is unusable for this item's quasi-coherent hypothesis. The delivered dependency module states the needed quasi-coherent clause through Mathlib's `SheafOfModules.IsQuasicoherent`.

## Earlier second reading (a previous round; superseded)

The statement and file were read together. `h` and `F` match the node's affine-morphism and quasi-coherent hypotheses; `0 < p` appears only on the higher-direct-image vanishing clause, while the edge-map clause quantifies all `p : ℕ`; the edge map is exactly the recorded identity h-map specialization. No mismatch was found.

## Second reading by R1

Independent object/hypothesis/conclusion checklist, read against the node and Stacks
coherent.tex lemma-relative-affine-vanishing (01XC) and
lemma-relative-affine-cohomology (089W), cohomology.tex lemma-apply-Leray (01F4),
and remark-explain-arrow (01FB, the map of Equation 01FA):

- Schemes X and S: `{X S : Scheme.{v}}`. Same arbitrary schemes; correct.
- Morphism h : X → S: `(h : X ⟶ S)`. Correct.
- Affine h: `[IsAffineHom h]`. Read Mathlib Morphisms/Affine.lean:
  inverse images of affine opens are affine. Exactly pqf-def-affine-morphism.
  A closed immersion is a parenthetical example, not an additional hypothesis.
  Mathlib IsClosedImmersion has the stated closed-embedding/surjective-stalk condition.
- O_X-module F: `(F : X.Modules)`. This is the same carrier as
  `SheafOfModules X.ringCatSheaf` and `(moduleRings X.toRingedSpace)`; correct.
- Quasi-coherent F: `[F.IsQuasicoherent]`. Read Mathlib Quasicoherent.lean,
  its local-cokernel presentation class, and landed Coherent.lean. The latter explicitly
  exposes Mathlib IsQuasicoherent and IsFiniteType for the first two clauses of
  pqf-def-coherent, and defines RingedSpace.IsCoherent for its third clause.
  Stacks modules.tex 01BE, 01B5, 01BV match these notions; on schemes the first is
  equivalent to the affine tilde characterization. No finite-type/coherent assumption.
- R^p h_* F = 0 for p > 0: the first conjunct quantifies `p : ℕ`, `0 < p`, and
  `IsZero (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).rightDerived p).obj F)`.
  Read PQFCohomology.lean and RingedSpaceDerivedDirectImage.lean: this is the
  module direct image right-derived functor specified by pqf-def-cohomology. Correct.
- Every nonnegative degree: the second conjunct quantifies all `p : ℕ`. Correct.
- The canonical edge map in the stated direction: `moduleCohomologyEdgeMap h F p`.
  Read ModuleCohomologyFMap.lean, including ModuleCohomologyFMapData.map and its
  identity specialization: source H^p(S,h_*F), target H^p(X,F), horizontal resolution
  map followed by inverse vertical map. It is the dependency's (c), not an arbitrary
  isomorphism. Correct.
- Isomorphism of O_S(S)-modules: `IsIso` of the recorded additive map together with
  `∀ r x, edge (r • x) = h.appTop r • edge x`. The explicit `@id` restores the
  target module carrier after the forgetful functor, without choosing an action.
  Source scalars are Γ(S,⊤); target scalars act through h.appTop. Additivity is already
  part of the edge map. Invertibility plus this scalar equation is exactly a module
  isomorphism, including linearity of its inverse. This clause was missing and is repaired.

No source-wide extra assumption: these Stacks lemmas allow all schemes, not just
Noetherian, separated, quasi-compact, field schemes or nonempty schemes. Removed the
HasDerivedCategory binders: rightDerived and the resolution-defined edge do not need
chosen derived categories. No variables or universes are unbound (autoImplicit false).

Edge cases: p=0 has the edge isomorphism and scalar equation, but no vanishing assertion.
The zero module and empty schemes are included. There is no index family to restrict;
no characteristic or field hypothesis. The arbitrary universe v is preserved, with
scheme/module carriers following the shared definitions. No test-object universe occurs.

Independent searches: msearch leanfinder, "affine morphism quasi coherent higher direct
images vanish Leray edge isomorphism", returned affine-limit/affine-site and pushforward
facts, no exact theorem. Loogle `SheafOfModules.IsQuasicoherent` confirmed Mathlib's
class and presentation declarations. LeanSearch "affine morphism higher direct image
quasi coherent cohomology comparison" was unavailable (HTTP internal server error).
`rg` with relative vanishing, affine cohomology, cohomology_edge and smul/linear over
Mathlib, WeilConjectures and lean/Sheaf found upstream DirectImage/AffineMorphism.lean
(vanishing only) and Affine/AffineMorphism.lean (field-linear isomorphism for k-schemes,
with abelian-sheaf cohomology and no identification with this edge map). Opened both:
neither states the node, so the item module is needed. The project's other cohomology
statements cite this node but do not state it. No second definition is introduced.

Mismatches and repairs: the delivered PqfDefCoherent module was the tautology
`[F.IsQuasicoherent] : F.IsQuasicoherent`, not the dependency's three defining clauses,
and duplicated an existing notion. Removed that module and dependency node copy;
imported the already landed Coherent module. The original IsIso conclusion was only
in AddCommGrpCat; added the scalar equation above. Removed unnecessary derived-category
binders, added the standard header, and expanded the theorem docstring to the node's
four proof steps, with their cited dependencies and the identification using λ=γ, β=id.
The original Worker report and historical dependency discussion remain above for history;
this section describes the final delivery, which has no dependency modules or new nodes.
The node's mathematical statement is unchanged; its lean.statement is the final signature.
