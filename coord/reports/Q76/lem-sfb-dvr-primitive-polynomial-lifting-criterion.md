## Worker report

The item is stated by `AlgebraicGeometry.symmetric_lifting_of_primitive_invariant_polynomials`
in `Sheaf.AlgebraicGeometry.DvrPrimitivePolynomialLiftingCriterion`. It has one theorem,
whose proof is `sorry`, and no additional theorem assumptions hidden in helper definitions.
The companion definition node supplies the missing general-ring coaction interface with real data.
No statement correction, disputed statement, or dependency repair was needed.

Hypothesis and clause correspondence:

- The DVR is `(A : CommRingCat.{u}) [IsDomain A] [IsDiscreteValuationRing A]`.
  Mathlib's class requires a local principal ideal domain which is not a field; its maximal
  ideal is `IsLocalRing.maximalIdeal A`.
- The group is `(H : Scheme.{u}) [H.Over (Spec A)]
  [GrpObj (H.asOver (Spec A))]`. The group diagrams are in the slice over this precise base,
  rather than absolute scheme products. The recorded general `GrpObj` interface applies
  without needing the original field specialization in the dependency's prose.
- Affineness over this affine base is `[IsAffine H]`: it is equivalent to the structure
  morphism being affine. Flatness is `[Flat (H ↘ Spec A)]`. Finite presentation is
  `[LocallyOfFinitePresentation (H ↘ Spec A)]` together with affineness, which supplies
  quasi-compactness and separatedness (hence quasi-separatedness). No smoothness,
  connectedness, reductivity, or completeness is imposed.
- The coefficient Hopf algebra is exactly `Γ(H, ⊤)`, with the canonical Mathlib instance
  from `Mathlib.AlgebraicGeometry.Group.Affine`. This is the construction recorded by
  `def-sfb-affine-coordinate-hopf-algebra`; no arbitrary Hopf structure is a parameter.
  An explicit `IsAffine H` binder makes that existing canonical instance inferable.
- A rational module is `RationalHopfModule.Coaction A Γ(H, ⊤) M`, with the actual linear map
  `M →ₗ[A] M ⊗[A] Γ(H, ⊤)`. Its two proof fields are precisely the counit and
  coassociativity identities, with Mathlib unitors and associator in the right-coaction
  convention. There is no restriction on the carrier's generation or flatness.
- `hprimitive` quantifies over every carrier `V : Type (max u w)`, additive group, module,
  free-module instance and finite-module instance. These last two assumptions mean finite
  free, without assuming a specified basis in the statement.
- Fixedness of `v` is `ρ.map v = v ⊗ₜ[A] 1`; primitivity is
  `v ∉ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A V)`, the actual maximal-ideal
  multiple of the module, not merely `v ≠ 0` or an injection from the ring.
- The hypothesis produces `n`, `1 ≤ n`, and `f : RationalHopfModule.degree A
  (Module.Dual A V) n`. Here degree is the power of the generator range in the same
  symmetric algebra used by the recorded universal-property and grading nodes.
- `dualMap` is constructed from Mathlib's finite basis and its dual: on the ith dual
  basis vector it is `sum_j e^j tensor S(c_ij)`, with `c_ij` obtained by applying the ith
  coordinate to `ρ(e_j)`. This is the contragredient, not the plain transposed action.
  There is no postponed theorem or existential choice of unspecified coaction data.
- The induced symmetric map is the universal algebra map extending `(ι tensor 1)ρ`.
  The equality `symmetricMap ... f = f tensor 1` means invariant homogeneous polynomial.
  Evaluation is `SymmetricAlgebra.lift (Module.Dual.eval A V v) f = 1`, which sends a
  product of linear forms to the product of their values at v, exactly as required.
- The conclusion's arbitrary carrier is `(M : Type w) [AddCommGroup M] [Module A M]`,
  with its rational coaction. Neither finite generation, freeness nor flatness is assumed.
- The quotient map is `(lam : M →ₗ[A] A)`, with `hλ : Function.Surjective lam`.
  `hequiv` is the coaction square evaluated on every m:
  `lam.rTensor Γ(H, ⊤) (ρ.map m) = lam m tensor 1`, exactly equivariance to the trivial module.
- The conclusion gives `n`, `1 ≤ n`, `q` in degree n, its symmetric coaction fixedness,
  and `SymmetricAlgebra.lift lam q = 1`. Under `Sym^n(A) ≃ A` sending the product of n
  scalars to their product, this last expression is exactly `Sym^n(lam)(q) = 1`.
  It does not ask for a degree-zero lift or for fixedness merely on A-valued group points.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, including inverse laws;
  exposed by `Mathlib.AlgebraicGeometry.Group.Affine`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom` and its
  affine-base/affine-source interpretation; `IsAffine H` expresses this equivalent form.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` (and `Spec.map` read).
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`;
  Basic/Map supply `TensorProduct.map`, `LinearMap.rTensor`, `lTensor`, `rid`, `lid`, `assoc`.
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`: `SymmetricAlgebra`, `ι`, `lift`,
  `algHom_ext`; these are the recorded symmetric-algebra universal-property interface.
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images`, whose grade-span and multiplication clauses
  identify the power of the generator range with the degree-n part. The helper module
  imports this recorded module publicly.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `def-sfb-affine-coordinate-hopf-algebra` records the existing canonical Hopf construction;
  its underlying `Mathlib.AlgebraicGeometry.Group.Affine` instance is used directly.
- The new node records `RationalHopfModule.Coaction`, `degree`, `symmetricMap`, `dualMap`.

The already stated proof dependencies are plain imports: Noetherian, Tilde,
ModulePullbackAffineSections, CoherentAffineSectionsFinite, GroupoidModuleLimitsColimits,
QuasiCoherentAffineSectionBaseChange, and ModuleCat.FilteredColimits. The two proof-only
nodes `lem-sfb-flat-noetherian-groupoid-coherent-approximation` and
`lem-sfb-dvr-rational-module-finite-free-cover` have no recorded Lean declaration, so no
nonexistent import is invented. They are not prerequisites for typing this statement.
The docstring carries all five proof steps of the item, including coherent approximation,
finite free resolution, primitivity, equivariant biduality and homogeneous evaluation.

Edge cases checked: the zero V has no primitive vector, so its premise is vacuous;
the zero M has no surjection onto a DVR; modules with torsion and modules of arbitrarily
large generation remain allowed; n = 0 is excluded in both occurrences; rank-one trivial
modules give the expected linear polynomial and lift. No residue characteristic is fixed.
The helper dual construction handles rank zero as the empty sum. Its `Nontrivial A`
condition is only on the finite-basis helper, and follows from the item's `IsDomain A`.
The polynomial tests lie in `Type (max u w)` so that finite covers built from ring
coefficients and an arbitrary `Type w` module fit without imposing an equality of universes.

Sources read: the node and all statement-dependency statements and Lean records;
Alper's online PDF https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf,
printed pp.521--523, Lemma 9.2.5, Remarks 9.2.4 and 9.2.7. The existing corrected node
already avoids the erroneous arbitrary-injection version of Remark 9.2.7: an injection
of multiplication by a nonunit cannot be separated with value 1. This delivery preserves
that correction verbatim. The current `literature/blueprint/latest/` was searched as well.

Searches actually run: msearch leanfinder on the full DVR implication returned symmetric
power generation and polynomial declarations, no lifting criterion; loogle
`SymmetricAlgebra, Bialgebra` returned `SymmetricAlgebra.instBialgebra`, which is the
additive-group Hopf structure on a symmetric algebra and is not an induced rational
coaction; grep `Comodule|contragredient|symmetricPowerCoaction` found no Mathlib hits.
For the helper, LeanSearch on ring coactions returned coalgebra coassociativity and
category-of-coalgebras declarations; LeanFinder on antipode-transpose dual coactions
returned Hopf antipode identities and tensor/dual matrix identities; Loogle
`"Comodule", "coaction"` returned zero hits. Mathlib, `lean/WeilConjectures`, `lean/Sheaf`,
the upstream declaration index and DAG were searched. Existing HopfAction and
RationalRepresentation coaction interfaces require fields; RelativeHopf.Coaction also
requires a field and a different relative action. Blueprint search `rational module`
returned only an unrelated stratified lattice node; ancestor lookup returns null.
The new node contains the actual tool outputs for its searches.

Validation: both delivered files were compiled separately through the prescribed
`scompile.py` against the live published build, in dependency order; no error or
unexpected warning remains. Module mode, explicit universe and variable binding,
source/blueprint docstrings, and the 100-character Lean line limit are used throughout.

## New nodes

`def-sfb-rational-hopf-module-data` defines general-ring right coordinate coactions,
homogeneous symmetric components, the induced symmetric algebra map, and the finite free
contragredient map. Source: Alper Lemma 9.2.5 and Remark 9.2.7, with the affine translation
of Stacks Tag 03LF. The three kinds of searches above and the DAG/blueprint search found
no existing general-ring interface. Existing field-only structures cannot be applied to
a DVR; the new definitions reuse Mathlib's tensor products, symmetric algebra, finite
basis, dual basis, coalgebra maps and antipode. All data are constructed, with no sorry.

## Second reading by Q76

This is a dispatcher-started direct delivery, with no second worker permitted by the
brief. This section records a second pass by the same worker; independent review is the
maintainer's review of the delivery, not a claimed independent review here.

I reopened the item and both module files and checked each clause above. The base is the
DVR itself, and GrpObj uses the slice over Spec A. Affineness plus local finite presentation
retains the full finite-presentation assumption. The coordinate Hopf structure is canonical.
Finite/free hypotheses occur only in the polynomial premise, and the arbitrary output
module has neither one. Primitivity is maximal-ideal nonmembership, both exponents are
positive, both fixedness equations are coaction equations, and evaluation is the algebra
lift of the specified linear form. The new node's dual formula has the required swapped
matrix indices and antipode. The actual homogeneous submodule agrees with the recorded
graded symmetric algebra. No node text or proof plan needed changing. During compilation
I added the Mathlib import supplying the strong rank condition for nonzero commutative
rings, changed the parser-reserved map identifier to `lam`, and expressed affineness as
`IsAffine H` to expose the canonical coordinate Hopf instance; these are implementation
repairs, with no added mathematical restriction. No other mismatch was found.
