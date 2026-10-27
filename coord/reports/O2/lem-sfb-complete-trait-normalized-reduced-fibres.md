## Worker report

The module `Sheaf.AlgebraicGeometry.CompleteTraitNormalizedReducedFibres` states
`AlgebraicGeometry.exists_completeTrait_normalized_reduced_fibres`. Its sole theorem has
proof `sorry`; its three public abbreviations contain the actual pullback, nilradical
reduction and composite structure maps. They are helpers for this node, not new notions.
The original node statement and dependency lists are unchanged.

Hypothesis and conclusion correspondence:

- A discrete valuation ring D: `(D : Type u) [CommRing D] [IsDomain D]
  [IsDiscreteValuationRing D]`. The class explicitly excludes fields.
- Complete for the maximal ideal: `[IsAdicComplete (IsLocalRing.maximalIdeal D) D]`.
- Its fraction field F: `(F : Type u) [Field F] [Algebra D F] [IsFractionRing D F]`.
- The scheme and its given morphism: `(X : Scheme.{u}) (f : X ⟶ Spec (.of D))`.
- Flat: `[Flat f]`; separated: `[IsSeparated f]`; finite type:
  `[LocallyOfFiniteType f] [QuasiCompact f]`. Properness is not required.
- A finite field extension L/F: existential `L`, `Field L`, `Algebra F L`, with
  `Module.Finite F L`. No separability condition occurs.
- The induced D-algebra structure is existential `Algebra D L` together with
  `IsScalarTower D F L`, which identifies it with the composite D → F → L.
- V is literally `integralClosure D L`, not an arbitrary ring with properties.
  This subalgebra has carrier `{x | IsIntegral D x}` and hence is the monic-polynomial
  construction in the node.
- V a DVR: existential `IsDiscreteValuationRing (integralClosure D L)`; its domain
  structure comes from the subalgebra of the field L. Completeness is
  `IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure D L)) (integralClosure D L)`.
- Fraction field L: `IsFractionRing (integralClosure D L) L`; finite D-module:
  `Module.Finite D (integralClosure D L)`.
- Local inclusion: `(IsLocalRing.maximalIdeal (integralClosure D L)).comap
  (algebraMap D (integralClosure D L)) = IsLocalRing.maximalIdeal D`.
  Injectivity is inherent: D embeds in F and then L, and the map to its subalgebra V
  is that same inclusion.
- X_V is the chosen `pullback f (Spec.map (.ofHom (algebraMap D V)))`.
  `f.reducedTraitBaseChange L` is exactly its `nilradical.subscheme`, namely H.
- N and nu are exactly `H.reducedNormalization` and `H.fromReducedNormalization`
  from the recorded dependency, including its empty coproduct convention.
- The maps to Spec V are `f.reducedTraitBaseChangeToBase L` (reduction inclusion
  followed by the second pullback projection) and
  `f.normalizedTraitBaseChangeToBase L` (nu followed by that map).
- H flat, separated, finite type: four conjuncts `Flat`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` of its specified structure map.
- N flat, separated, finite type: the same four conjuncts of its structure map.
- nu finite and surjective: `IsFinite H.fromReducedNormalization` and
  `Surjective H.fromReducedNormalization`.
- H_L geometrically reduced: `GeometricallyReduced (pullback.snd h (Spec.map
  (.ofHom (algebraMap V L))))`, where h is the displayed structure map of H.
  This is precisely the generic fibre's structure map to Spec L.
- N_L geometrically normal: for every `(Ω : Type u) [Field Ω] [Algebra L Ω]`,
  every stalk of `pullback n (Spec.map (.ofHom ((algebraMap L Ω).comp
  (algebraMap V L))))` is an `IsDomain` and `IsIntegrallyClosed` ring. Here n is
  N's structure map. Pullback pasting is the canonical identification with (N_L)_Ω.
- The closed fibre of N geometrically reduced: `GeometricallyReduced` of the
  second pullback projection along `Spec.map (.ofHom (IsLocalRing.residue V))`.
  `IsLocalRing.ResidueField V` is by definition V modulo its maximal ideal.
- Reduced has its usual Mathlib meaning: every section ring has no nonzero
  nilpotents (`AlgebraicGeometry.IsReduced`), as used in `GeometricallyReduced`.
- No hypothesis of affineness, reducedness, irreducibility or generic smoothness is
  present; no inhabitance assumption on X or its fibres is present.

Every variable is explicitly bound and `autoImplicit` is disabled. D, F, X, L and
all test fields are in the common arbitrary universe u, as in the project's scheme
base-change conventions. Any finite collection of given universes can be enlarged
into u, and field extensions of the same universe detect geometric normality:
a failed local integrality equation descends to a finitely generated subextension.
In particular the test-field universe is not independent below that of L or X.

Dependency declarations read and used (all imported publicly):

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-weil-proper-morphism`: its recorded companion `AlgebraicGeometry.IsSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (defined in Morphisms.Separated).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-integral-closure`: `integralClosure`,
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
- `def-pc-base-change`: `pullback` and `pullback.snd` with the projection convention
  of `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; the recorded module
  and its full docstring explicitly specify these objects, rather than requiring
  the module-pullback declaration in a scheme-only statement.
- `def-weil-pbc-scheme-reduction`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme` and `subschemeι`,
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `def-weil-pbc-reduced-normalization`: `Scheme.reducedNormalization` and
  `Scheme.fromReducedNormalization`, `Sheaf.AlgebraicGeometry.ReducedNormalization`.
  Its integral components and disjoint union are used without redefinition.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.

All recorded proof modules are imported plainly. The two proof-only nodes
`lem-sfb-geonormal-normalization-field-extension` and
`lem-sfb-normalization-affine-total-fractions` have no recorded Lean module yet;
their imports are left to the maintainer when those nodes are stated. Neither is
needed to type this statement. The theorem docstring contains all seven proof
steps, including generic preparation, the finite common extension, and the
comparison of the final normalization in a common total fraction ring.

Source check: Stacks `more-morphisms.tex`, the setup and theorem labeled
`theorem-normalized-base-change-with-reduced-fibre` (Tag 09IL), read locally;
Conrad Appendix Theorem A.2 and Remark A.3, printed p.28, read at
https://math.stanford.edu/~conrad/papers/qrg.pdf. A.2 explicitly contains the two
separate generic-fibre properties required here. No statement correction or
STATEMENT-DISPUTED flag is needed.

Edge cases checked: X empty (empty component set and normalization); empty special
fibre (e.g. a scheme supported on the generic point); disconnected or reducible X
(componentwise normalization); nonreduced X (reduce after base change, not before);
positive and mixed characteristic and imperfect residue fields (no separability
or perfection hypotheses); the identity field extension is permitted; D a field
is correctly excluded by the DVR definition. Normality is local, so no unintended
irreducibility requirement on the whole normalized scheme occurs.

Searches for an existing statement and helper names:

- `msearch.py leanfinder`: "normalized reduced base change of a flat finite type
  scheme over a complete discrete valuation ring has geometrically reduced special
  fibre" returned eight hits: relative normalization, Weierstrass good reduction,
  and ring geometric reducedness. None state this theorem.
- `msearch.py loogle`: `"IsDiscreteValuationRing", "normalization"`: zero hits.
- `msearch.py grep`: `normalized.*reduc|complete.*trait|geometrically.*reduced` in
  Mathlib/AlgebraicGeometry: 17 hits on geometric reducedness, none on this theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: normalized base-change and
  geometric-reducedness names found existing normalization constructions and
  preparation lemmas, but no complete-trait theorem with these conclusions.
- The exact item id has no hit in `lean/WeilConjectures`.
- `reducedBaseChange|reduced.*BaseChange|normalizedBaseChange|normalized.*BaseChange`
  in both project source roots finds unrelated private calculations, but none of
  the three newly introduced public helper names.

Validation: prescribed `scompile.py` compiled the sandbox module and its intended
library module cleanly (10.5 s and 11.6 s). An initial coercion ambiguity at the
stalk point binder was repaired using explicit `↥(...)`; no mathematical change.

## Second reading by O2

The dispatcher forbids starting another agent; no independent worker was spawned.
The maintainer's independent review remains the independent reading. I reread the
node and final signature clause by clause: D's completeness is for its own maximal
ideal; the existential is a finite field extension, allowing inseparable ones; V
is literally the integral closure; both model maps have all four required morphism
properties; finite and surjective refer to the actual componentwise normalization
map; the reduced generic, normal generic, and reduced special fibre clauses are
three separate conjuncts with the correct coefficient fields. The final special
fibre uses the quotient map of V rather than a chosen closed point. The helpers
only abbreviate the actual canonical constructions. No node wording changed.
