## Worker report

This is a substantive repair of the stage-2 packet returned at immutable head
4f0cd2829287. The saved packet was inspected and its prescribed initial dry run
passed (690ebafe6b), reproducing the reviewer's observation that the old statement
compiled despite missing semantic clauses. The repairs below change the Lean
statement and its canonical helper definitions; this is not an unchanged re-push.

Module: `Sheaf.TraceFormula.BoundedConstructibleDerivedHomContinuity`.
Main declaration:
`AlgebraicGeometry.Etale.bounded_constructible_derived_hom_continuity`.

The mathematical DAG statement, statement dependencies and proof are unchanged.
The node copy was refreshed from the current shared repository, retaining only the
new `lean` record; all non-`lean` fields were compared equal to that current copy.
The delivery wrapper supplies the commit on current `newtargets-dag`.

The module constructs the canonical derived Hom types, derived inverse-image
composition isomorphism, induced pullback map, limit leg, transition map and shift
transport. It defines a Prop structure with the two representative criteria for
continuity and the three compatibility equations. These are helper constructions
of this node, listed in `lean.declarations`, not new independent notions. Every
definition has real data. The sole theorem has the sole `sorry`; the previous
unnecessary degree-zero pullback-composition theorem and zero-Hom wrappers were
removed. The theorem docstring supplies all four proof steps and their DAG inputs.

The following is the complete hypothesis and conclusion correspondence.

| Node text | Lean rendering |
| --- | --- |
| Small nonempty directed index | `{I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`. The index uses the scheme universe as prescribed by the project. |
| Inverse system of schemes | `D : Iᵒᵖ ⥤ Scheme.{u}`. For `hij : i ≤ j`, `D.map (homOfLE hij).op` is the map from stage j to stage i. |
| Quasi-compact quasi-separated Noetherian stages | `[∀ i : Iᵒᵖ, IsNoetherian (D.obj i)]`. Mathlib's `IsNoetherian` extends `IsLocallyNoetherian` and `CompactSpace`; `IsLocallyNoetherian.quasiSeparatedSpace` supplies quasi-separatedness. Thus both qcqs clauses are included, with no separation assumption added. |
| Affine transition morphisms | `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]`. |
| X is the inverse limit | `(c : Cone D) (_hc : IsLimit c)`: X is `c.pt`, and its projections are `c.π.app (op i)`. The theorem applies to every chosen limiting cone, with no extra projection assumption. |
| Fixed stage i | `(i : I)`; all source objects live over `D.obj (op i)`. |
| Finite commutative coefficient ring | `{A : Type (u + 1)} [CommRing A] [Finite A]`, exactly the project's small-etale ModuleCat convention. |
| P_i and Q_i in the bounded derived category | `P Q : DerivedCategory (Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} A))`, with `hP.1 : DerivedCategory.TStructure.t.bounded P` and `hQ.1` for Q. This is the membership predicate defining `DerivedCategory.Bounded`. |
| Constructible cohomology sheaves | `hP.2 : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf ((DerivedCategory.homologyFunctor ... q).obj P)` and identically `hQ.2` for Q. This uses the precise recorded Sheaf-module declaration with a finite locally closed stratification, constructible parts, and finite module values. It does not use upstream `boundedConstructible` or `IsConstructibleSheaf`. |
| Termwise inverse images P_j, Q_j, P, Q | Each `boundedConstructibleDerivedHom f P Q n` is Hom between objects of `(upperStar (ModuleCat A) f).mapDerivedCategory`, with n-shift on its target. This is the localization of termwise exact inverse image. |
| Every integer n | `∀ n : ℤ, BoundedConstructibleDerivedHomContinuityData D c P Q n`; negative degrees and zero are included. |
| Canonical comparison is surjective | `descends`: each limit class is `boundedConstructibleDerivedHomLeg D c hij P Q n b` for some `j`, `hij : i ≤ j` and stage-j class b. |
| Canonical comparison is injective | `eventually_equal`: two representatives at j and k with equal legs have equal canonical transitions at one common later l. The paths to l agree since I is a preorder (proof irrelevance for the inequalities). |
| Isomorphism of abelian groups | The two preceding fields give bijectivity of the canonical filtered-colimit map. Every transition and leg is additive: it consists of the additive exact derived functor's map and pre/postcomposition by fixed comparison isomorphisms in a preadditive category. Hence this bijection is precisely an abelian-group isomorphism, rather than a comparison with an arbitrary set map. |
| Compatible with composition | `composition` quantifies a stage j, `hij`, target R, degrees m,p, `h : p + n = m`, a stage-j degree-n map a and stage-j degree-p map b. Its equation is `Leg hij P R m (ShiftedHom.comp a b h) = ShiftedHom.comp (Leg hij P Q n a) (Leg hij Q R p b) h`. All degrees occur because the outer theorem quantifies n. |
| Compatible with shifts | `boundedConstructibleDerivedHomShiftTransport f m n P Q a` is `(F.commShiftIso m).hom.app P ≫ a⟦m⟧' ≫ (shiftFunctorComm _ n m).hom.app (F.obj Q) ≫ ((F.commShiftIso m).inv.app Q)⟦n⟧'`, where F is exact derived pullback along f. The `shift` field quantifies j, hij, m and a at stage j; it says Leg of this transport is this transport of Leg, using the shifted source objects and shifted target objects on the left. Thus it is a commuting square between different Hom types and a genuine stage-to-limit comparison. |
| Compatible with passage to later stages | `later`: Leg at k after `boundedConstructibleDerivedHomTransition D hij hjk` equals Leg at j, with the cone equation and canonical derived composition comparisons. |
| No local-freeness, projectivity or finite-Tor restriction | There are no such binders or predicates. Constructibility permits arbitrary finite module values, not only free or projective values. |

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is a convention record, not a declaration to
  import. Its properties are `Scheme`, `IsNoetherian` and `IsAffineHom` from Mathlib.
- `lem-weil-pbc-limit-affine-transition` records
  `AlgebraicGeometry.exists_limit_affine_transition` in
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`. Its full signature and docstring
  were read: it produces a limiting cone, affine projections and restricted limits.
  Here the cone and its `IsLimit` proof are explicitly supplied, so this existence
  result is not invoked. The unused direct import was removed as requested in F3.
- `def-weil-pbc-derived-categories` records the module
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` and the existing
  `DerivedCategory`, `DerivedCategory.Bounded`, `DerivedCategory.homologyFunctor`
  and `AlgebraicGeometry.Etale.DerivedCategoryModule` encoding. That module is now a
  public import; boundedness is the existing standard-t-structure predicate.
- `def-weil-pbc-etale-constructible-sheaf` records
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` in
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, whose exact definition
  was read. It is a public import and is applied to each cohomology sheaf in hP/hQ.
  The different upstream module with the same declaration name is not imported.
- `def-weil-pbc-inverse-image` records `AlgebraicGeometry.Etale.upperStar` and its
  adjunction in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. The maps use
  it, `upperStarComp`, `Functor.mapDerivedCategoryNatIso` and
  `Functor.mapDerivedCategoryCompIso` from
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- The proof-only imports retain the stated proof plan: the constructible-sheaf
  Ext-continuity theorem, derived inverse-image coherence, Ext composition,
  truncation triangles, inverse-image exactness, filtered-colimit exactness, the
  five lemma and representable Hom exactness. Standard t-structure and exact-functor
  modules are already reached by the public imports.

Searches retained from the original packet (no duplicate theorem found):

- LeanFinder: “Derived Hom between bounded constructible etale complexes commutes
  with affine inverse limits of Noetherian schemes”; returned scheme-limit and
  scheme-morphism continuity lemmas, no derived-Hom continuity.
- LeanFinder: “Continuity of morphisms in the bounded constructible derived category
  of etale sheaves along inverse limits of schemes”; returned generic etale-site,
  scheme continuity and limit results, no matching theorem.
- Loogle: `"DerivedCategory", "colimit"`; zero hits.
- Mathlib grep: `constructible.*Hom|Hom.*constructible|bounded.*complex.*colimit`;
  hits concerned finite-presentation scheme maps and constructible subsets.
- LeanSearch: “Derived morphisms of constructible etale complexes commute with
  filtered inverse limit of schemes”; generic `colimitLimitIso` and scheme limits.
- Source and Sheaf `rg` searches found the sheaf-level
  `constructible_etale_ext_continuity`, which is a proof input and does not already
  assert continuity for bounded complexes.
- During this repair, `rg` for `ShiftedHom.comp`, `commShiftIso`, `shiftFunctorComm`,
  `DerivedCategory.Bounded` and `boundedConstructible` located the existing Mathlib
  operations and the upstream predicate that caused F3. File-only `#check` probes
  through scompile confirmed the types of `ShiftedHom.comp` and the shift
  comparisons. All probe files were removed from the delivery.

Edge cases reread against the repaired signatures: singleton and identity inverse
systems; empty schemes; zero complexes; degree zero and negative n; negative and
zero simultaneous shifts m; one-term shifted constructible sheaves; composites in
arbitrary integer degrees; distinct representatives needing a common later stage;
and finite-field towers. The stage j in composition and shift remains explicit
also for identity systems. Empty schemes and zero objects are admitted. The empty
index is deliberately excluded by the node. The ring can have zero divisors and
need not have invertible order on the schemes. No finite Tor assumption appears.

Universe check: I and schemes are in u; the finite ring and module carriers are in
u+1; derived Hom is `Type (u+1)` using the published derived-category instance.
There is no auxiliary universe equality or extra smallness hypothesis.

The final Lean signature is copied verbatim from the theorem keyword to before
`:=` into `lean.statement`. All eight delivered declarations are recorded in
`lean.declarations`. One theorem remains, with proof exactly `by sorry`; all seven
helper declarations have real bodies. The final scompile run of both sandbox and
module-path forms passed without errors or warnings (8.1 s / 9.0 s).
There is no statement correction, new node, dependency repair or disputed statement.

## Second reading by Q20

This is the required separate second pass by the single assigned worker; the brief
explicitly forbids starting another agent. I reopened the current node and complete
repaired Lean file and checked each clause against the table above, rather than
using compilation as a semantic check.

F1 was a real mismatch: the old shift equation unfolded a definition and its m was
unused. It is replaced by a real canonical shift-transport definition using
`commShiftIso m`, `a⟦m⟧'` and `shiftFunctorComm`, and a square equating Leg after
transport at j with transport after Leg. The left side uses shifted P and Q; the
right side starts from the image of a stage-j class. The equation is not the
unfolding of the pullback definition.

F2 was a real mismatch: the old composition equation used only identity pullback
on the limit, with no stage or limit leg. The new composition field quantifies
j and hij and compares Leg of `ShiftedHom.comp a b h` with `ShiftedHom.comp` of the
two legs. It covers arbitrary degrees n,p and their sum m. The unused old helper
theorem and degree-zero-only wrappers were removed.

F3 was a real mismatch: the old hP/hQ used upstream boundedConstructible, whose
cohomology predicate was not the recorded constructibility declaration. Each now
states standard boundedness conjoined with `∀ q, IsConstructibleEtaleModuleSheaf`
of its cohomology sheaf. The exact Sheaf declaration is used. The unused direct
LimitAffineTransition import is gone; the limit itself is still the cone c with
its IsLimit proof.

F4 is addressed by the explicit correspondence above. In this pass I checked:
the small nonempty directed index; Noetherian plus its qcqs consequences; all affine
transitions; a supplied limiting cone; fixed i; finite commutative A in Type (u+1);
the exact sheaf-module derived categories; boundedness and exact constructibility
for both P and Q; canonical termwise inverse images; all n in ℤ; descent and
common-stage eventual equality giving bijectivity of the additive colimit
comparison; arbitrary-degree stage-j composition; the simultaneous-shift square;
the later-stage square; absence of local-freeness/projectivity/finite-Tor binders;
all universes; verbatim lean.statement; the sole sorry-only theorem proof; and
source/blueprint docstrings with the four-step natural-language proof. No remaining
hypothesis or conclusion mismatch was found in this second pass.
