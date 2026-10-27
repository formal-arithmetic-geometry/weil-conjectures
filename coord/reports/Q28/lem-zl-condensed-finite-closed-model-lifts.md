## Worker report

The module `Sheaf.AlgebraicGeometry.CondensedFiniteClosedModelLifts` states
`AlgebraicGeometry.ProEtale.condensed_finite_closed_model_lifts` with a single
postponed theorem proof. Its three helper definitions construct the actual structure
map, actual retained closed-fiber map, and canonical restriction of a model
isomorphism. They introduce no alternative coefficient category, tensor, scalar
realization, henselian lift, or perfectness predicate. No node statement is changed.

The node and all its statement dependencies were read, including the signatures
and docstrings of their recorded declarations. Source checked from the local PDFs:
HRS Corollary 4.4(2) and the finite-component paragraph of Theorem 4.13; BS
Definition 2.2.10, Remark 2.2.11, Lemmas 2.2.12 and 6.1.1, and the henselian
assertion in the proof of Lemma 6.1.2. These give the prescribed extension argument
and the particular small-colimit lift. The proof docstring records all seven DAG
steps, including lifting both directions of the isomorphism and using faithfulness
for the inverse identities and uniqueness.

Hypotheses and conventions, clause by clause:

- A commutative condensed ring is `(Λ : Profinite.CondensedRing.{u})
  [IsCommMonObj Λ.X]`. This accepts arbitrary condensed rings, without a
  topological-ring presentation. `condensedScalarRing Λ.X` is precisely the
  reconstructed section ring Γ(*,Λ).
- For every scheme T, coefficients are `condensedRingObj Λ.X T`, from the existing
  `coefficientRing`/`upperStarFromPoint` construction. `DerivedCategory (Mod
  (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ.X T))` is the
  ordinary unbounded derived category of internal module sheaves, using the
  existing framework equivalence with sectionwise modules. No completed or
  bounded category is substituted. This is the same encoding as the recorded
  scalar realization and rigidity declarations; `ringedSiteModules` is publicly
  imported, and its recorded general-site category is not copied.
- `IsDualizable K` is the existing `Nonempty (HasRightDual K)`: evaluation,
  coevaluation and both triangle identities for the published derived tensor.
- `(A : Type u) [CommRing A]` supplies the affine scheme `Spec (.of A)`.
  `(ι : Type v) [Finite ι]` is any finite indexing set, including the empty set;
  no `Nonempty`, `Fintype`, or equality of index and ring universes is assumed.
- `I : ι → Ideal A` gives arbitrary ideals, with no finite-generation or
  radical hypothesis. `hcover : ∀ x : PrimeSpectrum A, ∃ a, I a ≤ x.asIdeal`
  says exactly that their underlying closed subsets cover Spec A.
- `Cbar : ι → Type u`, its commutative-ring and quotient-algebra instances,
  and the compatible A-algebra/scalar-tower instances give the affine maps
  Spec(Cbar a) → Spec(A/I a). The A-algebra and tower are the induced compatible
  structures, with no added existence condition. `Algebra.IndEtale (A ⧸ I a)
  (Cbar a)` and `Module.FaithfullyFlat (A ⧸ I a) (Cbar a)` express the given
  ind-etale faithfully flat covers. `IsWContractibleRing (Cbar a)` is the given
  w-contractibility of W_a.
- `K` belongs to the category for Spec A, with `hK : IsDualizable K`.
  `P : ι → DerivedCategory (ModuleCat.{u+1} (condensedScalarRing Λ.X))` gives
  independently prescribed scalar complexes; `hP` is exactly the recorded
  `DerivedCategory.IsPerfectRingComplex`, the bounded finite projective model
  predicate. No common model, common bounds or identification of P_a and P_b
  is required.
- The `α a` are actual derived isomorphisms to
  `(condensedScalarRealization Λ.X (Spec (.of (Cbar a)))).obj (P a)`.
  Their source is restriction along `closedModelFiberMap A (Cbar a) ≫
  closedModelLiftMap A (Cbar a)`. This composite is the original map W_a → X:
  its ring map is the retained A-algebra homomorphism composed with the
  A-structure map, which is the given A-structure map on Cbar a. Thus this
  does not change or constrain the input isomorphisms. Writing this equal
  composite directly avoids inserting a chosen or arbitrary identification.

Conclusions, clause by clause:

- C_a is exactly `Algebra.ClosedLift A (Cbar a)`, the already-defined small
  filtered-diagram colimit, in every occurrence of the conclusion.
  `Algebra.IndEtale A ...` is the first conjunct for every a.
- `Function.Bijective (Algebra.ClosedLift.reduction A (Cbar a) (I a))` asserts
  that the specified quotient reduction ring homomorphism is an isomorphism;
  it is not an existential unrelated ring equivalence.
- `HenselianRing ... ((I a).map (algebraMap A ...))` is the henselian-pair
  assertion for exactly I_a C_a. `IsWContractibleRing ...` is w-contractibility
  of V_a, using the same notion as for the prescribed W_a.
- `∃! e : ... ≅ ..., closedModelRestriction ... e = α a` states a unique
  derived isomorphism extending the specified α_a. Restriction is explicitly
  the derived image of `upperStarComp`, then `mapDerivedCategoryCompIso`, then
  pullback of e, then `discreteScalarExtensionPullbackIso`. These are the
  canonical coefficient-compatible composition and scalar comparisons, with
  actual definitions and no choice. The closed-fiber arrow is exactly
  `Spec.map (CommRingCat.ofHom (Algebra.ClosedLift.toAlgHom ...).toRingHom)`;
  the specified reduction assertion identifies its domain with the closed fiber.
- `WeaklyEtale (closedModelLiftMap ...)` expresses weak etaleness of each V_a → X.
  The inclusion of `Set.range (Spec.map (CommRingCat.ofHom
  (Ideal.Quotient.mk (I a))))` in its range says its image contains |X_a|.
- `IsAffine (∐ ...)` states that the actual finite disjoint union is affine.
  `Sigma.desc` is its induced map to Spec A; `Surjective`, `Flat`, and
  `QuasiCompact` give exactly the three claimed properties of that map.
- Membership of `Presieve.ofArrows ...` in `Scheme.proetalePrecoverage`
  is the existing pro-etale-covering predicate on the specified family.
  It includes the finite-affine-open fpqc condition, rather than only
  joint surjectivity or membership in a generated topology.
- The last two explanatory sentences are respected: there is no equality
  condition on different P_a and no claim about arbitrary closed subschemes
  of w-contractible schemes.

Dependency declarations used (module: declarations):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`,
  `Scheme.ProEt.topology`, `Scheme.proetalePrecoverage`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `upperStarFromPoint`, `condensedRingObj`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (imported exact sectionwise encoding); the internal-module encoding is the
  one used by the recorded scalar realization and its module equivalence.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` (the framework's existing standard instances).
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`.
- `Sheaf.AlgebraicGeometry.CondensedScalarRealization`:
  `condensedScalarRing`, `condensedScalarRealization`.
- `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport` and its public upstream import:
  the recorded same-universe clause `Algebra.IndEtale` (no universe transport
  is needed because all input affine rings inhabit the scheme universe u).
- `WeilConjectures.RingTheory.ProEtale.ClosedLiftMap` and its public import
  `...ClosedLift`: `Algebra.ClosedLift`, `Algebra.ClosedLift.toAlgHom`,
  `Algebra.ClosedLift.reduction`. The same colimit data are reused verbatim.
- `WeilConjectures.Mathlib.RingTheory.Henselian` and its Mathlib import:
  `HenselianRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`: `WeaklyEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `...QuasiCompact`:
  `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity`:
  `CondensedRing.discreteScalarExtensionPullbackIso`,
  `CondensedRing.henselian_lisse_rigidity` (the latter for the proof plan).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
  and `...Derived.UpperLowerStar`: `CondensedRing.upperStar`,
  `CondensedRing.upperStarComp`, and the exact induced `mapDerivedCategory`.
  The generic `Functor.mapDerivedCategoryNatIso` and
  `Functor.mapDerivedCategoryCompIso` supply the actual derived composition.
- `Mathlib.AlgebraicGeometry.Limits`: `Sigma.desc`, finite coproducts of
  schemes and the existing affine finite-coproduct instance.
- Plain proof imports retain the stated proof dependencies:
  `Sheaf.RingTheory.ProEtale.HenselianClosedLift`,
  `Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality`,
  `Sheaf.RingTheory.IndEtaleStability`,
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`, and
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`. Filteredness and reduction
  are in the publicly imported upstream `ClosedLift` module. The projective
  calculus proof node has no recorded Lean declaration at the time of reading;
  no proof-only prerequisite is restated in this stage-2 statement delivery.

Edge cases checked before writing: an empty index type forces Spec A empty by
`hcover`; the empty coproduct and empty pro-etale cover remain allowed.
A=0 is not excluded. I_a=A forces Cbar a to be the zero ring by its quotient
algebra structure; no nontriviality hypothesis excludes this case. I_a=0 is
allowed. Neither nonreduced A nor non-finitely-generated ideals are excluded.
The scalar ring may be zero, and scalar complexes may be zero or have arbitrary
bounds depending on a. The independent finite index universe is admitted by
Mathlib's smallness instance for finite types. No extra flatness assumption is
placed on Λ or its scalar ring, and no geometric finiteness hypothesis is added.

Searches actually made with the prescribed wrapper and local read-only searches:

- LeanFinder query: “Henselian lifts of w contractible covers of a finite closed
  covering extend prescribed perfect condensed sheaf models uniquely”. Eight
  hits on `Condensed.lanSheafProfinite`, explicit profinite presentations,
  `CondensedMod.ofSheafProfinite`, and light-condensed analogues. None states
  this model-lifting/finite-cover theorem.
- Loogle query: `Algebra.ClosedLift, HasRightDual`. The service responded
  “unknown identifier 'Algebra.ClosedLift'”; this is not evidence of absence.
  The upstream ClosedLift declaration was instead read directly and reused.
- Wrapper grep query: `henselian.*(condensed|lisse)|closedModelLift|closed_model_lift`.
  No Mathlib hits.
- LeanSearch query: “Prescribed perfect constant models extend uniquely from
  w contractible closed fibers to their henselian ind etale lifts”. Eight hits
  concerning `PerfectRing`/`Perfection` lifts of ring homomorphisms, none about
  perfect complexes or sheaf model lifts.
- Read-only `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `finite.*closed.*model|closedModelLift|closed_model_lift|` followed by the item
  id found unrelated algebraic-geometric model lemmas; no exact statement.
  `grep -rn` of the item id in `lean/WeilConjectures` found no attachment.
- `rg` for the four new declaration names in both source roots and
  `dag/lean_names_upstream.json` found no collision. Existing scalar,
  closed-lift, henselian-rigidity and pullback APIs were located and read
  directly rather than redefined.

Validation: the prescribed `scompile.py Q28 lem-zl-condensed-finite-closed-model-lifts`
compiled both its sandbox check and the library module with no errors or warnings
(the project suppresses the expected sorry warning). All variables and universes
are explicitly bound; `autoImplicit` is false. No proof is supplied beyond real
construction of the three canonical maps/comparisons. No statement dispute or
source correction was needed.

## Second reading by Q28

A separate pass compared the written theorem with the node, checking every input
and every conclusion listed above. It checked the endpoints and directions of
all four isomorphisms in `closedModelRestriction`: composite pullback to iterated
pullback, then pullback of the model, then scalar comparison to L_W(P). It checked
that uniqueness is equality of actual derived isomorphisms, not only isomorphism
classes or cohomology groups, and that the reduction is the specified map. It also
checked that the given map W_a → X is unchanged by its factored presentation,
that image containment uses the quotient closed immersion, and that the final
cover predicate applies to the original finite family. No mismatch was found.
This was an in-session second pass; the dispatch brief forbids starting another
agent and assigns the independent review to the maintainer.
