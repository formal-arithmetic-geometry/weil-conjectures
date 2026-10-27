## Worker report

The module `Sheaf.RingTheory.StrictHenselizationResidueAutomorphismLift` states
`Algebra.strictHenselization_residue_automorphism_lift`, with `sorry` as its entire
proof. It defines no new objects and proves nothing. The six accepted proof steps
are carried into the theorem docstring. The mathematical statement and accepted
stage-1 split are unchanged.

Hypotheses and conclusions, clause by clause:

- The henselian normal local domain H is `[CommRing H] [HenselianLocalRing H]
  [IsDomain H] [IsIntegrallyClosed H]`. HenselianLocalRing includes locality;
  IsIntegrallyClosed is exactly the recorded normal-domain convention.
- The residue field kappa is `IsLocalRing.ResidueField H`. The chosen separable
  closure is `K` with `[Field K] [Algebra (IsLocalRing.ResidueField H) K]
  [IsSepClosure (IsLocalRing.ResidueField H) K]`. The H-algebra structure and scalar
  tower state that its base map is the residue map followed by the field inclusion.
- R is a local domain and an H-algebra. The parameter
  `P : StrictHenselizationPresentationIn.{u, u} H K R` is the existing pointed-etale
  universal colimit presentation. `P.residueMap` is its specified map to K, constructed
  from the pointings, and hence the residue identification in the node. No arbitrary
  residue map is substituted. The statement adds the already landed definition node
  `def-sc-ring-strict-henselization` to stmt_deps, as allowed by brief-stage2 section 5.
  This is the ring presentation already used by the finite-lift dependency, which
  identifies it with the recorded scheme strict henselization, respecting residues.
- F and L have `[IsFractionRing H F]` and `[IsFractionRing R L]`. Their algebra
  structures and towers state the usual compatible embeddings H into R into L and
  H into F into L. These name the canonical fraction-field extensions; they impose
  no finiteness, normality or separability assumption on L/F.
- Omega has `[Field Ω] [Algebra F Ω] [IsSepClosure F Ω]`. Its H-structure is compatible
  with F. `j : R →ₐ[H] Ω` and `_hj : Function.Injective j` are the given H-embedding.
- Tau is `τ : K ≃ₐ[IsLocalRing.ResidueField H] K`, exactly Gal(K/kappa).
- The witnesses `t : R ≃ₐ[H] R` and `tL : L ≃ₐ[F] L` are the requested automorphisms.
  The first two conjuncts say respectively that t reduces to tau and that tL extends t.
- `jL : L →ₐ[F] Ω` is characterized by
  `∀ r, jL (algebraMap R L r) = j r`. Since L is a fraction field, this determines
  exactly the extension of the given embedding. `g : Ω ≃ₐ[F] Ω` and
  `∀ x, g (jL x) = jL (tL x)` say that g restricts to tL under that embedding.
- The last clause universally quantifies over a diagram D indexed by the full
  subcategory of `finiteResidueLiftIndex H K` on `Normal kappa e.val`. Finiteness is
  in the existing index, separability is inherited from K/kappa, and Normal supplies
  the Galois condition. `_local`, `_finite`, `_etale` say each D.obj e is a finite
  local etale H-algebra. The surjective `q e` with kernel m_H B_e and the displayed
  scalar equation give exactly its specified residue identification with e.
  For finite local etale algebras over henselian H, m_H B_e is the maximal ideal.
- `c : Cocone D`, `IsColimit c`, and `i : c.pt ≅ CommAlgCat.of H R` express the given
  colimit identification as an H-algebra identification. The following equation
  requires its compatibility with the specified residue maps. In particular, the
  naturality of c forces every transition to induce the inclusion of its residue
  fields inside K. No extra transition-action hypothesis is assumed.
- `ts` supplies each H-algebra automorphism t_e. Its first conjunct says it reduces
  to tau restricted to e, by equality inside K (so no separately chosen restriction
  map is needed). The second conjunct is uniqueness among all H-automorphisms with
  that reduction. The third conjunct is commutation with every diagram transition.
  The final conjunct says t agrees with ts on every colimit coprojection, exactly
  the assertion that their induced colimit automorphism is t.

The final clause uses an arbitrary diagram on the Galois indices with the stated
finite/local/etale/residue data. It does not assume the stronger `lift_unique` or
`map_unique` fields of `StrictHenselizationFiniteLiftSystem` as hypotheses. Those
properties must be derived in stage 3 from full faithfulness, as the node's proof says.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded terminology;
  Mathlib `HenselianLocalRing` and `HenselianRing` provide the ordinary notions.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain`, is the recorded normal-domain specialization.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem`; its signature and docstring identify
  Mathlib `IsSepClosure` as the closure notion and provide finite separable subfields.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, `strictHenselizationScheme`, and
  `strictHenselization_properties`; their affine pointed-neighbourhood colimit
  is compared to the ring presentation in `Algebra.strictHenselization_finite_lifts`.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn` and its canonical `residueMap`.
- `Sheaf.RingTheory.StrictHenselizationFiniteLifts`:
  `Algebra.finiteResidueLiftIndex` appears in the statement;
  `Algebra.strictHenselization_finite_lifts` supplies the proof's finite-stage
  presentation, including its residue and Galois-cofinality clauses.
- Proof imports: `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`
  (`Algebra.IsHenselizationAtPrime'`),
  `Sheaf.RingTheory.HenselianFiniteEtaleMapBijective`
  (`CommAlgCat.FiniteEtale.bijective_baseChange_residueField_map_of_henselianLocalRing`),
  `Mathlib.FieldTheory.Normal.Basic` (`AlgEquiv.liftNormal` and
  `AlgEquiv.liftNormal_commutes`). Mathlib `IsSepClosure.isGalois` states the recorded
  separable-closure normality fact. The ordinary colimit input is Mathlib's `Cocone`
  and `IsColimit`, whose desc/fac/uniq signatures were read.

Sources inspected: Stacks pione.tex, lemma-identify-inertia (0BSW), especially the
paragraph identifying Aut(A^sh/A^h) with residue Galois automorphisms; algebra.tex,
remark-construct-sh-from-h (0BSL) and lemma-henselian-cat-finite-etale (04GK).
The newest blueprint's `rem-dl-a1-conventions` retains the extension-across-infinity
versus trivial-inertia equivalence served by this auxiliary statement. No change
to the blueprint unit is needed.

Edge cases checked: H a field (the stages are then the residue subfields themselves);
separably closed kappa (the residue Galois group is trivial); tau the identity;
imperfect residue fields (only IsSepClosure, never IsAlgClosed K, is assumed);
positive characteristic; non-Noetherian H; and nonnormal L/F. The finite Galois index
is nonempty because it contains the base field, so no empty-diagram case is excluded.
H, K and R use the dependency's common arbitrary universe u; F, L and Omega have
independent universes v, w and z. There is no quantification over undersized test
rings or forced equality between the fraction-field or ambient-field universes.

Searches actually run for this assignment:

- msearch leanfinder, query “Every automorphism of the residue separable closure lifts
  to the strict henselization and extends to a separable closure of the fraction
  field”: 8 hits, including galLift, galLiftEquiv, IsSepClosed.lift and
  IsLocalRing.ResidueField.mapAut. None states the henselian finite-etale/colimit
  automorphism assertion.
- msearch loogle, query `IsSepClosure, AlgEquiv`: one hit, `IsSepClosure.equiv`,
  an isomorphism between closures, not the required residue lifting statement.
- msearch grep, query
  `[Hh]enseli.*([Aa]utomorphism|[Aa]lgEquiv)|([Aa]utomorphism|[Aa]lgEquiv).*[Hh]enseli`:
  zero hits.
- msearch leansearch, query “Residue automorphisms lift uniquely to finite etale
  algebras over a henselian local ring and to the strict henselization”: 8 hits,
  including residue-field lift maps, formally-unramified uniqueness for nilpotent
  ideals, and ResidueField.mapAut; none states this assertion.
- rg in both project Lean roots for strict-henselization automorphisms, residue
  automorphisms, the presentation and finite-lift system. It finds the existing
  presentation and finite lifts reused above. `StrictHenselianFractionInertia` is
  a DVR specialization with additional assertions, not this normal-local theorem.
  `HenselianGlobalInertiaComparison` is the downstream comparison, whose proof needs
  this assertion; it cannot replace this node. Direct upstream grep for the item
  id, and name-clash searches in both Lean roots and dag/lean_names_upstream.json,
  return no matching declaration.

No new nodes or dependency modules are necessary. No STATEMENT-DISPUTED issue found.
The inherited “already split and reviewed by Q26” ending concerned stage 1; the
current queue lists this item at stage 2 with no Lean attachment. The accepted split
is preserved exactly apart from the added statement dependency and Lean record.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
