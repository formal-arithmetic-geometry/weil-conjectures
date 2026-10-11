## Worker report

The module `Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality` states
`AlgebraicGeometry.koszul_open_orthogonality`, with proof `sorry`. Its supporting module
`Sheaf.AlgebraicGeometry.AffineKoszulObject` defines the actual sheafified Koszul object;
its data is fully specified. The only supporting `sorry` is the named functor-law theorem
`affineKoszulTilde_map_comp`, whose docstring gives its proof by Mathlib's existing
`tilde.map_comp` after unfolding the two category-instance presentations. No mathematical
notion is replaced by arbitrary data.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme is `X : Scheme.{u₁}`. The open immersion `j : U → X` is represented by the
  open `U : X.Opens` and its canonical immersion `U.ι`; this represents any open immersion
  up to the canonical isomorphism with its image.
- The affine open `V = Spec A` is represented by `A : Type u₁`, `[CommRing A]`, and
  `a : Spec (.of A) ⟶ X` with `[IsOpenImmersion a]`. This retains the choice of affine
  coordinate ring and identification, rather than replacing it by global functions on X.
- `X = U ∪ V` is `hcover : U ⊔ a ''ᵁ ⊤ = ⊤`.
- `U ∩ V` is the open `a ⁻¹ᵁ U` of `Spec A`; `hqc : IsCompact (...)` is exactly
  quasi-compactness of that overlap. Open immersions identify its topology with the
  corresponding open of X.
- The finite list is `r : ℕ` and `f : Fin r → A`, including the empty list.
- `Z = V \ U = V(f₁,...,fᵣ)` is stated pointwise as
  `hZ : ∀ x : PrimeSpectrum A, x ∉ a ⁻¹ᵁ U ↔ ∀ i : Fin r, f i ∈ x.asIdeal`.
- The Koszul object is `affineKoszulObject A r f`, not a freely chosen perfect object.
  `ExteriorAlgebra.koszulComplex` has term `⋀[A]^q (Fin r →₀ A)` and differential
  contraction with `Finsupp.linearCombination A f`. The natural finite free module
  `Fin r →₀ A` is A^r. `ComplexShape.embeddingDownNat` puts homological degree q in
  cohomological degree -q and extends by zero in positive degrees. This is the usual
  cochain presentation of the node's exterior-degree-q Koszul complex. Termwise tilde
  and `DerivedCategory.Q.obj` make it an object of D(O_V). Boundedness and perfection
  follow from the finite exterior powers; they are descriptions of this fixed complex,
  not extra assumptions on a variable K.
- `E : schemeDerivedCategory (Spec (.of A))` with
  `hE : schemeDerivedQCohProperty (Spec (.of A)) E` says exactly E ∈ D_QCoh(O_V).
- `R` and `adj` present Rj_* as a right adjoint to the existing exact derived restriction
  `(SheafOfModules.overFunctor ... (a ⁻¹ᵁ U)).mapDerivedCategory`. For an open immersion,
  restriction is exact, and its derived right adjoint is derived direct image.
  Right adjoints and their adjunctions are unique up to the unit-compatible natural
  isomorphism. Thus quantifying over this presentation introduces no mathematical
  restriction, no different action, and no arbitrary map E → Rj_*j^*E. Invertibility of
  the unit is invariant under the unique comparison of such presentations. The derived
  categories on the localized open site and on the open ringed space are equivalent.
- Clause (i) is `IsIso (adj.unit.app E)`, the canonical restriction unit itself.
- Clause (ii) is `∀ n : ℤ, Subsingleton ((affineKoszulObject A r f)⟦n⟧ ⟶ E)`.
  Each Hom is an additive group containing zero, so Subsingleton means precisely that
  every morphism is zero. `↔` states the two implications.
- The two `HasDerivedCategory.{w₁}` binders specify the shared localization on V and
  on its overlap. These are the established project carrier/universe convention,
  not additional geometric hypotheses.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory` and
  `schemeDerivedQCohProperty`; their full definitions were read.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsStrictlyPerfect`, `Scheme.IsPerfect`,
  and `Scheme.perfectSubcategory` were read. This node describes the constructed K as
  perfect; it does not quantify over an arbitrary perfect K, so no separate `IsPerfect`
  hypothesis or unused import is inserted.
- `Sheaf.CategoryTheory.WeakTriangulatedGenerator`: both generator definitions were read.
  The present equivalence does not assert that K generates all of D_QCoh(V); it uses
  ordinary Hom vanishing, so this contextual dependency requires no predicate in the
  signature and no unused import.
- `Sheaf.Paper.KoszulComplex`: `ExteriorAlgebra.koszulComplex`, `koszulBoundary`, and
  their full signatures/docstrings were read and reused.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.map`, `tilde.functor`,
  `tilde.map_id`, `tilde.map_comp`, `tilde.map_zero` (the existing associated-sheaf notion
  carried by `lem-weil-pbc-spec-module-tilde-sections`).
- `Mathlib.Algebra.Homology.Embedding.Extend`: `HomologicalComplex.extend`, with the
  existing `ComplexShape.embeddingDownNat`.
- `Sheaf.Paper.DerivedHomMayerVietoris`, imported transitively by DerivedCategory:
  `moduleRings` and the shared exactness/additivity instances of `overFunctor`, reused
  unchanged to form derived restriction.

Edge cases checked before stating:

- r = 0: the empty vanishing condition is true at every prime, so hZ forces the overlap
  empty; K is O_V in degree zero. The unit is E → 0 and the assertion detects E = 0
  by affine cohomology, as required.
- All fᵢ = 0: again the overlap is empty; K is the finite exterior complex with zero
  differential and contains O_V. The criterion remains detection of the zero object.
- A unit among the fᵢ: hZ forces the overlap to be all V, the Koszul complex is acyclic,
  and the restriction unit is invertible; both conditions hold.
- E = 0: both conditions hold. Empty V / the zero ring is allowed: no nontrivial-ring,
  nonempty-spectrum, domain, characteristic, reducedness or Noetherian hypothesis occurs.
- No connectivity, regular-sequence, or positive-r restriction is introduced. Arbitrary
  unbounded E is allowed. The Hom and derived-category universe w₁ is explicit.

Source inspected: https://stacks.math.columbia.edu/tag/09IR (Lemma 36.15.2), including
its proof and the reference to Situation 36.9.1. The local Stacks source checkout is
absent on this machine, so the official Stacks page was opened. Its affine X corresponds
to this node's V, and its U to this node's U ∩ V. No statement correction is needed.

Searches made (also captured in sandbox searches.jsonl):

- LeanFinder: `Koszul complex orthogonality derived category open immersion` gave eight
  generic K-projective/K-injective orthogonality and derived-fraction hits, no criterion.
- Loogle: `KoszulComplex, DerivedCategory` gave zero hits, unknown KoszulComplex.
- LeanSearch: `Koszul complex sheaves derived category` was unavailable (HTTP internal
  server error); the unavailability is recorded, not interpreted as a negative result.
- msearch grep: `Koszul|koszul` in Mathlib/AlgebraicGeometry gave zero hits.
- LeanFinder: `the Koszul complex sheafified on Spec of a commutative ring as an object
  of the derived category` gave tilde and unrelated relative-differentials/local-cohomology
  hits. Existing tilde is reused; none defines its application to a Koszul complex.
- rg in all Mathlib and WeilConjectures found Koszul sign rules, the projective-line
  two-term sequence, and a regular-sequence TODO, not the present construction or theorem.
- rg in lean/Sheaf found the landed algebraic `ExteriorAlgebra.koszulComplex`, reused.
- rg in DAG and `tools/blueprint_refs.py search koszul` found no definition node for
  the sheafified affine Koszul object. The blueprint search listed ten other Koszul
  usages. Upstream-name search and the item-id search in WeilConjectures found no match.
- Full-name searches for affineKoszulObject, affineKoszulTilde and
  koszul_open_orthogonality found no existing declaration.

Both modules compiled together cleanly on the server (3.5 seconds). Every theorem proof
is `sorry`; no proof is supplied at this stage. No STATEMENT-DISPUTED issue was found.

## New nodes

`def-pc-affine-koszul-object` defines the actual Koszul object on Spec A, using the
existing algebraic Koszul complex and existing termwise tilde construction, then the
shared derived localization. Source: Tag 09IR with the algebraic construction in Tag
0622. The search results above show that the algebraic complex already has a node and
is not duplicated, while its sheafified derived object has none. The helper
`affineKoszulTilde` only transports Mathlib's unchanged tilde objects and maps from
`Scheme.Modules`' category instance to the shared `SheafOfModules` category instance;
it does not give a second associated-sheaf construction. Its functor composition law
is a named theorem with `sorry` and a full proof plan, as required for proof obligations
of definitions. This node is a direct statement dependency of the item.

## Second reading by C1

I independently opened the item's node copy, both delivered Lean modules, all six
underlying dependency nodes, and the declarations listed below. The statement agrees
with the node and the source; no Lean, node, or signature change was necessary.

Source reading: the repository has no local Stacks checkout. I fetched the official
Stacks source `perfect.tex` and `more-algebra.tex` from
https://github.com/stacks/stacks-project into this item's scratchpad and read
`lemma-orthogonal-koszul-complex` (Tag 09IR), `situation-complex` (Situation 36.9.1),
the beginning of `section-koszul`, and `definition-koszul` (Tag 0622).
I also independently opened https://stacks.math.columbia.edu/tag/09IR and
https://stacks.math.columbia.edu/tag/0622. Situation 36.9.1 assumes only a commutative
ring and a finite sequence, and defines the open as the union of the basic opens.
No Noetherian, regularity, nontriviality, characteristic, or boundedness hypothesis
on E is implicit there. The source's affine X is the node's V, and its open U is
the node's overlap. The source explicitly changes chain degree q to cochain degree
-q with the same differential; the node's exterior-degree description is rendered
with exactly that convention, rather than a complex with differential of wrong degree.

Object, hypothesis, and conclusion checklist:

1. Arbitrary scheme X: `(X : Scheme.{u₁})`. Verdict: the recorded Mathlib Scheme,
   with arbitrary explicit universe; no separatedness or finiteness assumption.
2. Open immersion j:U into X: `(U : X.Opens)` and its canonical inclusion `U.ι`.
   Verdict: every open immersion identifies its source with this open subscheme;
   neither injectivity alone nor a different geometric morphism is substituted.
3. Affine open V=Spec A: `(A : Type u₁) [CommRing A]`,
   `(a : Spec (.of A) ⟶ X) [IsOpenImmersion a]`.
   Verdict: same affine coordinate ring and its identification with the open image.
4. Cover X=U union V: `hcover : U ⊔ a ''ᵁ ⊤ = ⊤`.
   Verdict: exact equality of opens; not an unrelated cover or vacuous hypothesis.
5. Quasi-compact overlap: `hqc : IsCompact (a ⁻¹ᵁ U : Set (Spec (.of A)))`.
   Verdict: compactness here is quasi-compactness without Hausdorff assumptions;
   the open immersion identifies this set with U intersection V.
6. Finite list including the empty list: `(r : ℕ) (f : Fin r → A)`.
   Verdict: no positive-r or nonzero-element condition.
7. Closed complement Z=V(f):
   `hZ : ∀ x : PrimeSpectrum A, x ∉ a ⁻¹ᵁ U ↔ ∀ i : Fin r, f i ∈ x.asIdeal`.
   Verdict: exactly the same underlying closed subset, not an equality of ideals
   or an unnecessarily specified closed-subscheme structure. By negating the
   right side, the overlap is the union of D(f i), as Situation 36.9.1 requires.
8. The specified perfect Koszul object K: `affineKoszulObject A r f`.
   Verdict: its fully specified data uses `ExteriorAlgebra.koszulComplex A r f`,
   then `extend ComplexShape.embeddingDownNat`, termwise tilde, and
   `DerivedCategory.Q.obj`. The dependency's terms are `⋀[A]^q (Fin r →₀ A)`;
   its differential is contraction with `Finsupp.linearCombination A f`.
   The embedding is explicitly n ↦ -n. Exterior powers above r vanish and all
   terms are finite free, so boundedness and perfection describe this fixed K;
   they are not missing hypotheses on an arbitrarily chosen complex.
9. Arbitrary E in D_QCoh(O_V): `(E : schemeDerivedCategory (Spec (.of A)))`
   and `hE : schemeDerivedQCohProperty (Spec (.of A)) E`.
   Verdict: precisely quasi-coherent cohomology in every integer degree, read
   from the recorded definitions; no coherence or boundedness assumption added.
10. Canonical derived restriction/direct-image map: `R` and
    `adj : (SheafOfModules.overFunctor ... (a ⁻¹ᵁ U)).mapDerivedCategory ⊣ R`.
    Verdict: derived restriction is the existing exact restriction functor on the
    localized open site. Its right adjoint is Rj_*, up to the unique compatible
    natural isomorphism. This presentation is legitimate: such a right adjoint
    exists for sheaves of modules, and changing the adjunction presentation
    transports the unit by an isomorphism. The arrow is not freely quantified.
11. Clause (i): `IsIso (adj.unit.app E)`.
    Verdict: isomorphism of the canonical E → Rj_*(E restricted to the overlap).
12. Clause (ii): `∀ n : ℤ, Subsingleton ((affineKoszulObject A r f)⟦n⟧ ⟶ E)`.
    Verdict: Hom from K[n], with all positive and negative shifts, vanishes.
    The Hom group contains zero, so Subsingleton expresses vanishing exactly.
13. Equivalence and quantifier order: clauses (i) and (ii) joined by `↔`, after
    arbitrary E and its quasi-coherent-cohomology hypothesis. Verdict: both
    implications are present, and n is quantified inside the vanishing clause.
14. The two `HasDerivedCategory.{w₁}` instances specify the shared derived
    localization on V and its overlap. Verdict: the project's established
    universe convention, not additional geometry, a chosen abelian instance,
    a derived category of quasi-coherent modules, or an independently duplicated
    D(O_V). The explicit universes u₁ and w₁ and all variables are bound.

Dependency inspection: I read `schemeDerivedCategory`, `schemeDerivedQCohProperty`,
`schemeDerivedQCohCategory` in `Sheaf.AlgebraicGeometry.DerivedCategory`;
`Scheme.IsStrictlyPerfect`, `Scheme.IsPerfect`, and `perfectSubcategory` in
`Sheaf.AlgebraicGeometry.PerfectComplex`; and both generator predicates in
`Sheaf.CategoryTheory.WeakTriangulatedGenerator`. Perfection and generation are
context here: the item does not ask to quantify over a perfect object or assert
that K generates all D_QCoh(V), so no extra predicates or unused imports belong
in its signature. I read the terms and boundary construction of the recorded
`ExteriorAlgebra.koszulComplex` in `Sheaf.Paper.KoszulComplex`; Mathlib's `tilde`,
`tilde.map`, `tilde.map_id`, `tilde.map_comp`, and `tilde.functor` in
`Mathlib.AlgebraicGeometry.Modules.Tilde`; and the existing `embeddingDownNat`.
I opened `Scheme.Modules` and its Category instance and the shared `moduleRings`
and exactness/additivity instances in `DerivedHomMayerVietoris` to check the
category-instance transport rather than trusting the helper's name.

New-node review: `def-pc-affine-koszul-object` introduces the actual sheafified
Koszul derived object, absent from the DAG and existing library. Its statement
matches the source construction term by term, including the cochain indexing.
The algebraic complex and the associated-sheaf functor already have nodes and
are reused, not redefined. Its helper functor uses exactly `tilde M` and
`tilde.map g`; the distinct Scheme.Modules category presentation explains why
Mathlib's tilde functor cannot simply be used as a functor into the shared
SheafOfModules carrier. The only postponed helper is the named composition-law
theorem, whose docstring explains transport of Mathlib's existing map_comp law.
No definition data is sorry. The theorem proof and the item's proof are both
sorry; no theorem was proved. Each declaration has its source and blueprint id.
The item docstring follows all three proof steps (cone, power tuples/detection,
converse adjunction). All Lean lines have at most 100 characters.

I checked the new node's fields against brief-stage2 §5: definition/split, matching
id/file/chapter/unit, exactly the four cited statement dependencies, empty proof
and proof_deps, null proof_origin/mathlib_match, worker creation record, none
lean audits, recorded searches and Lean record. `blueprint_refs.chain` confirms
its ancestor is lem-sc-finite-duality and its full via chain agrees with the
record, including the item as its first intermediate node. There are no
additional dependency modules or statement_change records to review.

Edge cases: r=0 makes hZ say the overlap is empty and makes K the unit sheaf in
degree zero; the unit E → 0 is invertible exactly when affine cohomology detects
E=0. All f i=0 gives the same empty overlap with the exterior zero-differential
complex containing the unit summand. A unit among the f i gives full overlap and
an acyclic K. E=0 satisfies both sides. The zero ring permits an empty affine V;
X itself may be empty, and U may be empty or all X. No field, domain, nonzero-ring,
regular-sequence, reducedness, characteristic, or nonempty-spectrum restriction
occurs. Arbitrarily unbounded E and every integer n are covered. Using u₁ for
Spec A and X does not restrict the size of affine coordinate rings: the project
permits arbitrary universes and an affine chart of a Scheme.{u₁} has coordinate
ring in that same universe. No independent universe bounds a testing family.

Independent searches (recorded by msearch in searches.jsonl):

- LeanFinder: `A finite exterior contraction complex detects whether the restriction
  adjunction unit is invertible`. Eight hits concern exterior-power functors,
  projective resolutions, and unrelated exactness; none is this criterion.
- Loogle: `"tilde"`. Twelve hits include `AlgebraicGeometry.tilde`, `tilde.functor`,
  `tilde.map`, and its adjunction. I opened the declarations: these give the
  associated-sheaf construction already reused, not the Koszul derived object.
- LeanSearch: `associated sheaf of the finite Koszul complex on an affine scheme`.
  Service unavailable (Internal Server Error); no negative verdict inferred.
- rg with koszul/Koszul in Mathlib/AlgebraicGeometry, the complete upstream
  WeilConjectures tree, and project's AlgebraicGeometry modules found sign rules
  and the projective-line short exact sequence, not this affine criterion.
  A full-tree search for the new full names and for associated/sheafified Koszul
  constructions found no declaration. The upstream projective-line sequence is
  specialized to two homogeneous coordinates and is not a candidate match.
- DAG searches for Koszul objects and sheafified Koszul constructions, together
  with `blueprint_refs.py search Koszul`, found algebraic complexes, adic
  completion constructions, and uses in other theorems, not a node already
  carrying the sheafified object on an arbitrary Spec A.

Mismatches and changes: none. Both node lean.statement strings were checked
verbatim against their file signatures. The supporting module and item compiled
together on the server with scompile.py in 3.4 seconds, exit 0, no warnings.
