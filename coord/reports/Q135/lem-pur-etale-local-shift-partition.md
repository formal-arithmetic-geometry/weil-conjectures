## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` defines the explicit set
`AlgebraicGeometry.Scheme.etaleLocalShiftLocus` and states
`AlgebraicGeometry.Scheme.etaleLocalShiftPartition`, with its proof `sorry`.
The helper is exactly the union of images defined in the item's statement; its data
are the set comprehension `∃ i, shift i = n ∧ y ∈ Set.range (f i)`.
No theorem is proved, and no definition contains postponed data.

Hypotheses, individually:

- A nonzero finite commutative ring is `(A : Type u) [CommRing A] [Finite A]
  [Nontrivial A]`. No topology on A is an additional input.
- The scheme is `(Y : Scheme.{u})`; the small pro-etale site and constant coefficient
  module derived category are the existing `proEtaleDerivedCategory Y A`.
  This uses the actual small site, with object universe u+1 and morphism universe u,
  and the standard localization of `SheafOfModules` over the constant ring of ULift A.
- `K : proEtaleDerivedCategory Y A` is arbitrary. `_hK` says precisely that
  `{q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor ... q).obj K)}` is finite.
  There is no Noetherian, quasi-compact, constructibility, Tor, or common-shift hypothesis.
- The arbitrary covering family is `I : Type v`, `U : I → Scheme.{u}`,
  `f : ∀ i, U i ⟶ Y`, with `[∀ i, Etale (f i)]`.
  `_hcover : ∀ y, ∃ i, y ∈ Set.range (f i)` is exactly joint surjectivity.
  The independent index universe v allows arbitrarily large families.
- `shift : I → ℤ` gives the n_alpha, and `L` gives actual module sheaves over
  the constant ring on each U i. `_hlocal` uses the existing intrinsic predicate
  `IsLocallyConstantProEtaleModuleSheaf` (dependency record repaired below).
- `_hrank` supplies a pro-etale covering family V_j of each U_i and module-sheaf
  isomorphisms `(L i).over (V j) ≅ SheafOfModules.unit (A_Ui.over (V j))`.
  Thus it states exactly local isomorphism to the constant coefficient ring AS A MODULE.
  The coefficient ring in the signature is spelled out as `sheafCompose` forgetting
  commutativity of `proEtaleConstantRing`; it is the same ring as in L's category.
  No chosen global basis, constant global model, or geometric-stalk-only substitute is used.
- `_hshape` is `Nonempty ((proEtaleConstantRingDerivedPullback A (f i)).obj K ≅
  ((DerivedCategory.singleFunctor ... 0).obj (L i))⟦shift i⟧)` for every i.
  This is exact termwise constant-coefficient inverse image and the usual cochain shift,
  so the surviving cohomology degree is minus the shift.

Conclusions, in conjunction order:

1. `(range (f i) ∩ range (f j)).Nonempty → shift i = shift j` is the overlap assertion.
2. `Pairwise (fun n m ↦ Disjoint (etaleLocalShiftLocus ... n)
   (etaleLocalShiftLocus ... m))` is pairwise disjointness for distinct integers.
3. `∀ n, IsClopen (etaleLocalShiftLocus ... n)` states both open and closed.
4. `(⋃ n, etaleLocalShiftLocus ... n) = Set.univ` is union equal to all of |Y|.
5. `Set.Finite {n | (etaleLocalShiftLocus ... n).Nonempty}` is the exact finite-support
   assertion; it does not bound labels carried by empty covering members.
6. A nonempty n-locus implies `¬ IsZero ((DerivedCategory.homologyFunctor ... (-n)).obj K)`.
7. Every nonempty U_i has `Set.range (f i) ⊆ etaleLocalShiftLocus ... (shift i)`.
8. Joint surjectivity remains after restricting the index type to
   `{i : I // Nonempty (U i)}`. This renders “the other covering members may be discarded.”

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`; its full signature is the functor from an abelian
  category's chosen derived category back to that category in integer degree n.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, and the standard localization convention.
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`:
  `DerivedCategory.singleFunctor` and the shift convention imported from the derived API.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.Paper.ProEtaleLocallyConstantSheaf`:
  `AlgebraicGeometry.Scheme.IsLocallyConstantProEtaleModuleSheaf`,
  `proEtaleConstantModuleSheafOver` (the latter is used by the former's definition).
- The already landed node `def-weil-pbc-proetale-operations` is added to stmt_deps;
  its recorded module `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` gives
  `proEtaleConstantRingDerivedPullback`, `proEtaleConstantRingPullback` and the actual
  canonical constant-section coefficient comparison. Its public ring-sheaf interface gives
  `proEtaleRingModules` and `proEtaleConstantRing`. No canonical map is an extra input.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientModulePullback_exact` and its commutative
  tensor comparison are imported for the planned proof. The statement uses the already
  published exact tensor inverse image in the intrinsic presentation, whose equivalence
  to the transported action is exactly the constant-exact dependency's commutative clause.

All stated proof-dependency modules are imported, including the module stalk functor,
constant stalk, inverse-image stalk, and weakly-etale localization. Mathlib leaves supply
Fpqc, EtalePoint, UniversallyOpen, and the already imported pullback and WeaklyEtale API.
The unstated `lem-fix-weakly-etale-algclosed-section` is a proof-only prerequisite,
so contributes no import; its use is retained in the full natural-language proof docstring.

Edge cases checked before writing and again against the signature:

- Y empty, including an empty index type: all loci and all images are empty, support
  is empty, the union is all of the empty space, and every pointwise clause is vacuous.
- Empty cover members can carry arbitrarily many labels. Neither the hypothesis nor
  conclusion bounds those labels; only NONEMPTY shift loci must have finite support.
- Over one geometric point, K = A[3] has surviving degree -3; the conclusion uses `(-n)`.
- A disjoint union of two components with different shifts is allowed; connectedness,
  a uniform shift, quasi-compactness, and surjectivity of each individual f_i are absent.
- K zero on a nonempty Y cannot satisfy the rank-one local shapes when A is nonzero.
  The zero ring is intentionally excluded, since otherwise different shifts could overlap.
- Arbitrary finite non-fields and rings with zero divisors remain allowed.

Searches (2026-10-17):

- `msearch.py ... leanfinder "A bounded complex etale locally rank one in a single varying
  degree determines a finite clopen partition by its shift"`: eight hits, including
  `CochainComplex.exists_iso_single`, `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`,
  and `exists_clopen_partition_of_clopen_cover`. None states this geometric shift theorem.
- `msearch.py ... loogle '"IsLocallyConstant", "isClopen"'`: one hit,
  `IsLocallyConstant.isClopen_fiber`; it assumes an existing locally constant function,
  whereas this theorem must construct its shift loci from the local shapes.
- `msearch.py ... grep '(shift|cohomolog).*(clopen|locallyConstant)|
  (clopen|locallyConstant).*(shift|cohomolog)'`: zero hits in Mathlib.
- `msearch.py ... leansearch "finite clopen partition by shifts of locally rank one
  sheaves in a bounded derived category"`: eight hits, generic clopen partitions,
  sheaf functors, derived Ext size and t-structure facts; no exact statement.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf` for
  `IsLocallyConstantProEtale|rankOne|RankOne|shift.*[Pp]artition|[Ss]hift[Ll]oc`:
  existing local-constancy predicates and the affine-line invariance proof discussion,
  no separate shift-partition theorem. Upstream item-id search gives no hit.
- Read the existing intrinsic/fixed local-constancy, constant-ring operations, exactness,
  and concentrated-complex declarations and their docstrings before choosing interfaces.
  These searches avoided duplicating any of those definitions.

Validation: `scompile.py Q135 lem-pur-etale-local-shift-partition <module>` passed
sandbox and library-layout compiles with no errors or warnings (5.3 s and 6.7 s).
The only postponed proof in this delivery is `etaleLocalShiftPartition`.
No statement correction, disputed statement, or new DAG definition is needed.

## Dependency modules

`def-weil-proetale-locally-constant-sheaf`: lean-only repair under §1(B), using an
EXISTING declaration, so no dependency module is delivered or duplicated. Its recorded
`IsLocallyConstantProEtaleFixedModuleSheaf` takes `Sheaf ... (ModuleCat A)`, which cannot
accept the intrinsic `SheafOfModules` objects of the recorded `proEtaleDerivedCategory`.
The exact existing `IsLocallyConstantProEtaleModuleSheaf` states the same arbitrary-model
cover-local constancy over the restricted constant ring, and was already publicly imported
by the fixed-coefficient module. Rebind to that declaration, with its exact full signature
and lean.note; all other fields of that dependency node remain unchanged.

## Second reading by Q135

Author's separate self-check, with the node and completed module reopened; the maintainer
provides the independent review. No second agent was started, as required by the brief.
I matched each binder and all eight conjuncts to the node as listed above. In particular,
the local rank-one condition uses isomorphisms in the localized MODULE category, the same
ring-sheaf module category is used in K, L and cohomology, and exact pullback is the
published canonical functor with no variable coefficient identification. The shift sign
is positive in the local-shape hypothesis and negative in the cohomology conclusion.
The overlap assertion refers to intersections of the ORIGINAL images, not only the
constructed loci. Pairwise disjointness, both topological properties, exhaustivity,
finite nonempty support and the nonzero-cohomology implication are independent conjuncts.
The empty-member conclusion explicitly retains joint surjectivity after their removal.
The dependency record repair was checked against the whole definition: arbitrary constant
module models may vary by cover member, and no ring/module finiteness was inserted there.
No semantic mismatch was found on this rereading. Only lean is changed for that dependency;
the item changes lean and adds the already landed operations node to stmt_deps.
