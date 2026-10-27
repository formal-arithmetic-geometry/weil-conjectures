## Worker report

The module `Sheaf.CategoryTheory.LatticeKoszulInjectiveNormalization` states
`Profinite.DiscreteLattice.InjectiveNormalization.lattice_koszul_injective_normalization`,
together with the inclusion naturality and injective quasi-isomorphism clauses. All three
theorems have `sorry` proofs. Its only new definition, `resolutionValueIso`, is the existing
universal derived computation isomorphism specialized to a bounded-below termwise injective
complex, with real data throughout. The definition chooses a lower bound from the complex's
existing boundedness proof, applies Mathlib's theorem that bounded-below complexes of
injectives are K-injective, and uses the recorded derived-value isomorphism. It chooses no
resolution, invariant object, Koszul complex, or unconstrained comparison map.

Read the item's complete statement and seven proof steps, every statement dependency's
statement and Lean record, and the source signatures and docstrings used below. The current
blueprint is `literature/blueprint/latest/blueprint/sec-six-functors-basics/` followed by
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
That paragraph supplies the direct-image route; the detailed lattice calculation is the
item's explicitly agent-formulated expansion, as its source record already says.

Hypotheses and clauses correspond as follows:

- Arbitrary commutative condensed coefficients are `(R : Profinite.CondensedRing.{u})`
  and `[IsCommMonObj R.X]`. This is the tensor ring-object encoding on the coherent
  profinite site, not a restriction to coefficients represented by a topological ring.
  The single explicit universe `u`, `AddCommGrpCat.{u+1}` coefficients in the recorded
  module category, and `DerivedCategory.{u+2}` localization in its instances implement
  the size convention. There is no independent smaller universe or extra size equality.
- Every nonnegative rank is `r : ℕ`; the main theorem fixes a family `K : ∀ r, KoszulModel
  R r`, and its conclusion gives simultaneous comparisons for all ranks. This merely
  collects the node's rankwise choices; no compatibility between different ranks is added.
  The recorded `Group r = Multiplicative (Fin r → ℤ)` is the lattice with its ordered
  basis. `Equivariant R r` and `Modules R` are precisely the recorded lattice-action and
  original internal-module categories. The discrete action presentation is the one
  already fixed by the dependency, with invariants the actual action-diagram limit.
- The finite Koszul terms and differential are those of `KoszulModel`, not another
  model. `TriangulatedCup.total` uses Koszul degree first and differential
  `d_K + (-1)^a d_P`; `totalInclusion` is the actual invariant augmentation in degree
  zero with the `(0,n)` total inclusion. Its previously recorded coordinate definition
  is used directly.
- Naturality of the invariant inclusion is `inclusion_naturality`, on every actual
  cochain map. The equation is `Γ(f) ≫ b_P' = b_P ≫ K(f)`.
- Every bounded-below termwise injective J is
  `(J : CochainComplex.Plus (Equivariant R r)) [∀ n : ℤ, Injective (J.obj.X n)]`.
  `inclusion_quasiIso` asserts `QuasiIso (totalInclusion ... J.obj)` and also supplies
  the instance needed to invert its localized map. There is no K-injectivity hypothesis:
  it is obtained from the given lower bound and termwise injectivity inside the helper.
- The formula is the third conjunction of the main theorem. For every monomorphic
  quasi-isomorphism `s : P.obj ⟶ J.obj`, it states
  `onComplex P ≫ (resolutionValueIso J s).hom = Q(Ks) ≫ inv (Q(b_J))`.
  Here `resolutionValueIso : RΓ(QP) ≅ QΓ(J)` is exactly the canonical computation
  identification `η_J⁻¹ RΓ(Qs)`, including the quotient-to-Q isomorphisms. Thus the
  displayed equation is exactly the node's inverse-inclusion formula in its specified
  value model. `Mono s` and `QuasiIso s` are retained. Writing P as a Plus complex loses
  no case: a monomorphism to a bounded-below J forces every term below J's bound to be
  zero, so any source permitted by the node already has this boundedness property.
- Independence of resolutions and lifts is encoded by the quantifier order: `M` and
  `c` are fixed before *all* J and s. `onComplex` is computed solely from M and P, while
  every resolution formula is equated to that same arrow after the canonical value
  identification. `M.iso` is a natural isomorphism on all derived morphisms, so no
  representatives or lifts occur in the resulting comparison.
- `M : ∀ r, TriangulatedCup.TriangulatedModel ...` supplies the triangulated total
  descent, its factorization of QK, and `M.iso` to the restriction of ordinary RΓ.
  `M.factorShiftCompatibility` and `M.shiftCompatibility` retain precisely the coherent
  signed total shifts and the fixed unit-normalized derived shifts. Thus this is the
  comparison of triangulated functors on D-plus with values in the ordinary derived
  category. It is not a collection of degreewise cohomology isomorphisms.
- `ComparisonProperties.connecting` identifies the actual boundary of every termwise
  short exact Koszul module sequence with RΓ of the canonical module boundary, followed
  by the specified shift. The predicate explicitly asserts the short exactness of both
  relevant complex sequences and uses `DerivedCategory.triangleOfSESδ`, with its -p cone
  convention. No sign is left to a freely chosen connecting map.
- `c : ∀ r, Comparison ...` supplies the simultaneous natural module comparisons.
  `ComparisonProperties.extendsModules` identifies them with the components of M using
  the single-complex isomorphism fixed by its nonzero-row coordinate equation.
  `Comparison.normalization` is `Q(K.augmentation.app P) ≫ c.iso.hom.app P = invariantUnit
  ... P`; `ComparisonProperties.normalization` also gives this unit equation for every
  bounded-below complex. These are the invariant-inclusion normalizations in the node.
- `TriangulatedCup.IsRankZero R (K 0) (M 0)` asserts the identity normalization for all
  bounded-below complexes at rank zero. Its invariant identification is explicitly the
  limit inclusion, its total identification is explicitly the empty-subset coordinate,
  and its final equation is `onComplex P = Q(k.hom) ≫ Q(e.inv) ≫ derivedUnit P`.
  Consequently after the normalized derived-identity identification the arrow is the
  identity. It does not allow arbitrary rank-zero identifications.
- The final conjunction is the requested equality for every s, with the target transport
  written explicitly: `onComplex P ≫ RΓ(Qs) = Q(Ks) ≫ onComplex J`. Cancelling the
  canonical RΓ(Qs) identification gives exactly the node's final formula.

Dependency declarations reused (source signatures and documentation read):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its inherited module
  action/category structure. `def-weil-size-convention` is a metatheoretic convention
  without a declaration; the explicit universes above implement it.
- `Sheaf.CategoryTheory.CondensedActionModule`: the recorded internal `Modules` and
  section-action setup, through the exact lattice specialization below.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: the recorded ordinary
  invariant-derived calculus (import retained as a statement dependency).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q` and `quotientCompQhIso`.
- `Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution`: `Modules`, `Group`,
  `Equivariant`, `invariants`, `KoszulModel`, `derivedInvariants`, `derivedUnit`,
  `invariantUnit`, `resolutions` and `Comparison`.
- `Sheaf.CategoryTheory.LatticeKoszulTotalTriangles`: its total/shift/triangulated
  framework and canonical SES boundary calculation. That module publicly reexports
  the existing constructions in `Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison`:
  `total`, `totalInclusion`, `TriangulatedModel`, `onComplex`, `ComparisonProperties`,
  `IsRankZero`. They are reused; the old existence theorem there is not an exact match
  for this item's explicit injective quasi-isomorphism and every-resolution formula.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso` defines the helper's real data.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` (through the imported
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`):
  `CochainComplex.isKInjective_of_injective`. The same derived module's
  `CochainComplex.IsKInjective.Qh_map_bijective` is the recorded closed-upstream proof
  dependency `lem-weil-pbc-kinjective-hom-derived`.
- Remaining stated proof dependencies are imported privately:
  `WeilConjectures.Algebra.Homology.FiniteStripAugmentation`
  (`HomologicalComplex₂.quasiIso_of_finite_strip_row_augmentation`),
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
  (`Adjunction.preservesKInjectiveComplexes`),
  `Sheaf.CategoryTheory.KInjectiveFiberTriangleComparison`
  (`existsUnique_unitNormalizedKInjectiveShift` and the recorded triangle comparisons),
  and `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
  (`DerivedCategory.triangleOfSESδ`).
  `lem-sfb-condensed-action-injective-infrastructure` has no Lean record in the read
  node; it is a proof dependency only, and no missing declaration from it is needed
  to type this statement. The required objects and computation are already supplied
  by the listed recorded statement dependencies.

The existing total/shift declarations currently live in the older triangulated-cup
comparison module. Accordingly no reciprocal proof import from that module to this new
module should be added: it would make an import cycle. This delivery changes no existing
source or dependency record.

Edge cases checked before writing: r=0 has only the empty subset and its canonical
identity normalization is retained for all bounded-below complexes, not only modules.
The finite-strip row bound must be r+1, since degree r can be nonzero. Lower bounds may
be any integer, including negative values. The zero module, zero ring and zero complex
are included, and inverses then mean the unique identity arrows of zero objects. No
characteristic assumption or division is introduced; signs still make sense in
characteristic two. Maps and resolutions are quantified without choosing any lift.

Searches actually run using the prescribed `msearch.py` for this item:

- LeanFinder: "Invariant inclusion into lattice Koszul totalization of injective
  complexes defines a normalized triangulated comparison with derived invariants".
  Eight hits, including `DerivedCategory.TStructure.t` and generic triangulated/homological
  functor and complex factorization results. None states the lattice comparison formula.
- Loogle: `CategoryTheory.Functor.rightDerivedNatIso, NatTrans.CommShift`.
  Zero hits; service reports unknown identifier `NatTrans.CommShift`. This search did
  not establish absence; the actual declarations were read in local sources.
- Mathlib grep: `koszul.*(injective|invariant)|invariant.*koszul`.
  Zero hits.
- LeanSearch: "The invariant inclusion into a finite Koszul total complex of injectives
  computes derived invariants naturally". Eight hits, including total-complex inclusions
  and generic model-category injective factorization; no match for the normalized theorem.
- Project `rg` over `lean/WeilConjectures` and `lean/Sheaf` with the same Koszul/invariant
  expression and `lattice_koszul_injective_normalization` found the existing Koszul module
  and triangulated-cup infrastructure described above and unrelated ring-theory injective
  linear maps. Searching the item ID in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json` found no existing declaration of this item.

No new nodes, dependency repairs, statement corrections, or statement disputes are needed.
The sandbox node copy changes only `lean`. The module compiled cleanly via `scompile.py`
in both sandbox and final library-module modes; only the permitted theorem sorries remain.

## Second reading by Q90

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
