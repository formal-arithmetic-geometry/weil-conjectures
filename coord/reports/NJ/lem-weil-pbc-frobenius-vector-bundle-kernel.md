## Worker report

The module `Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel` states
`AlgebraicGeometry.Scheme.frobenius_vectorBundle_kernel_constructible`, with a single
`sorry` proof. It is precisely the Noetherian specialization of Stacks Project,
More on Étale Cohomology, Tag 0GKU, `lemma-frobenius-linear-on-vb` (the source TeX
was read). No definition, source statement, or dependency record was changed.

Hypothesis and conclusion correspondence:

- Prime p: `(p : ℕ) [Fact p.Prime]`.
- Scheme S: `(S : Scheme.{u})`.
- Scheme over F_p: `[S.Over (Spec (.of (ULift.{u} (ZMod p))))]`.
  The lift places the prime field in the scheme universe; it carries the same field
  operations and excludes no scheme universe, including u = 0.
- Noetherian means quasi-compact and locally Noetherian, exactly
  `[CompactSpace S] [IsLocallyNoetherian S]`. No separation condition is added.
- The O_S-module is `(E : S.Modules)`; finite local triviality with varying finite
  rank is `[E.IsFiniteLocallyFree]`. The existing upstream predicate is defined by
  locally free local-generators data with a finite generator family on each member
  of the cover; it does not require a common rank. Local freeness already supplies
  the quasi-coherence required by `Modules.etaleTensorSectionsSheaf E`.
- E_et is the dependency's exact tensor-pullback section sheaf, composed with
  `sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}`.
  This is the sectionwise ULift of the given sheaf, without sheafification or
  any replacement of tensor pullback by another module pullback.
- F is a morphism from that lifted abelian sheaf to itself; hence it is additive
  and commutes with restrictions on every small étale object.
- Semilinearity is `hF`: for every `U : S.Etaleᵒᵖ`, lifted structure-ring section
  `a : ULift.{u + 1} Γ(U.unop.left, ⊤)` and lifted module section
  `e : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)`,
  applying F to `ULift.up (a.down • e.down)` equals the lift of
  `a.down ^ p • (F.hom.app U e).down`. This explicitly transports scalar action
  along the two lift bijections. Both lifts use exactly universe `u + 1`.
  The explicit `@id` only fixes the section module type for instance synthesis;
  it is the identity function, without a cast to a different object.
- Coker(F-1)=0 is `IsZero (cokernel (F - 𝟙 _))` in the abelian sheaf category.
- Constructibility of Ker(F-1) is
  `IsConstructibleAbelianSheaf (kernel (F - 𝟙 _))`, the dependency's global finite
  constructible locally closed partition with finite locally constant abelian values.
- No invertibility, positive rank, globally fixed rank, or nonemptiness binder occurs.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Spec`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`:
  `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf`; its complete
  definition and the underlying `etaleTensorSectionsPresheaf` were read.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, specialized to
  `S.smallEtaleTopology` and `AddCommGrpCat.{u + 1}`.
- `Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleAbelianSheaf`; its full definition
  was read, including inverse images and the global partition.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, the existing varying-rank predicate.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`,
  already used by the dependency's section sheaf.
- `Mathlib.Algebra.Category.Grp.Ulift`: `AddCommGrpCat.uliftFunctor`, preserving
  limits and hence the sheaf condition through `sheafCompose`.

Every recorded proof dependency module is imported. The proof nodes
`lem-weil-pbc-locally-noetherian-quasi-separated`,
`lem-weil-pbc-abelian-sheaf-epi-locally-surjective`, and
`lem-weil-pbc-etale-covering-base-change` have no Lean record yet and thus no
proof import is available. They are still present in the unchanged DAG proof plan.
The theorem docstring includes all seven steps of that plan.

Edge cases checked: the empty scheme admits the empty global partition; rank zero
has the identity solution cover, zero kernel and zero cokernel. F = 0 gives F-1 = -1,
so also has zero kernel and cokernel. F need not be invertible. Locally varying ranks
are permitted by the actual upstream class. Prime p excludes characteristic zero and
nonprime exponents. Arbitrary u, including u = 0, is allowed. A kernel is formed in
abelian sheaves, not in O_S-linear morphisms (F is generally not O_S-linear).

Searches for an existing statement:

- `msearch.py ... leanfinder` query: “Frobenius semilinear endomorphism vector bundle
  etale sheaf kernel constructible cokernel zero”. Eight hits, chiefly étale
  Kähler differential results, with no vector-bundle fixed-point theorem.
- `msearch.py ... loogle` query `frobenius, LinearMap`. Two hits:
  `LinearMap.frobenius` and `LinearMap.frobenius_def`; these define Frobenius on
  an algebra, not the two sheaf conclusions.
- `msearch.py ... grep` query `frobenius.*(kernel|cokernel)|constructible.*frobenius`:
  zero Mathlib hits.
- `rg` of the source project and `lean/Sheaf` for
  `frobenius.*(kernel|construct)|Frobenius.*(kernel|bundle)`: no matching theorem;
  only an unrelated Weil-group text and a curve Artin–Schreier cohomology model.
- `grep -rn` of the item id in source `WeilConjectures`: no hits.
- `rg` of Mathlib, source, side declarations and `dag/lean_names_upstream.json`
  for the selected declaration name: no collision.
- Searches of local-freeness declarations located the upstream varying-rank
  `IsFiniteLocallyFree` class and the existing DAG node
  `def-sc-finite-locally-free-sheaf`; no new notion or duplicate definition is needed.

Server verification uses only `scompile.py`, with nice 19, two threads, and the
60-second per-file limit. The complete module compiled cleanly in 2.5 seconds
before final metadata/preflight, with no unexpected warnings. No local Lean
compiler or library build was run. No statement dispute or correction is needed.


## Second reading by NJ

I independently read the node, its seven proof steps, Stacks more-etale.tex at
lemma-frobenius-linear-on-vb (Tag 0GKU), the five statement-dependency nodes and
their declarations, and the delivered module. The source introduces no additional
standing hypothesis in this section. It treats arbitrary schemes over F_p; the
node explicitly chooses the Noetherian specialization needed for its finite global
partition convention. The Lean preserves precisely that specialization.

The complete object/hypothesis/conclusion checklist is:

1. A prime p: `(p : ℕ) [Fact p.Prime]`. Pass; neither an arbitrary characteristic
   exponent nor an invertibility hypothesis replaces primality.
2. A scheme S over F_p: `(S : Scheme.{u})` and
   `[S.Over (Spec (.of (ULift.{u} (ZMod p))))]`. Pass. I opened Mathlib's Scheme
   declaration. The lifted prime field has exactly the same operations; the base
   lift lets it lie in the scheme universe, including u = 0.
3. S is quasi-compact and locally Noetherian: `[CompactSpace S]` and
   `[IsLocallyNoetherian S]`. Pass. I opened the class in Mathlib Noetherian.lean:
   it requires Noetherian rings on affine opens, equivalent to the dependency's
   affine-cover formulation. Compactness supplies exactly quasi-compactness;
   there is no separatedness or finite-type assumption.
4. An O_S-module E, locally finite free with rank allowed to vary:
   `(E : S.Modules) [E.IsFiniteLocallyFree]`. Pass. I opened upstream
   ModuleCat/Sheaf/LocallyFree.lean and Mathlib's locally free data class.
   The upstream class requires locally free generator data and finite generator
   families on each covering member, without one fixed rank. It implies local
   freeness and quasi-coherence, so the latter is not an added hypothesis.
5. Its associated abelian étale sheaf: each endpoint of F is
   `(sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
   (Modules.etaleTensorSectionsSheaf E)`. Pass. I read that definition and the
   underlying `etaleTensorSectionsPresheaf` in EtaleTensorSections.lean: at U it
   is exactly Γ(U, u^*E), using `Modules.tensorPullback`, with the unit-normalized
   restriction maps. I also opened TensorPullback.lean: its object is extension
   of scalars of the inverse-image module, rather than Mathlib's other pullback.
   No replacement sheaf or private section construction occurs here.
6. F is additive and a morphism of sheaves: its displayed arrow is in
   `Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}`. Pass. The dependency's
   Mathlib Sheaf category uses natural transformations with additive components.
7. Semilinearity for all local scalar and vector sections: `hF` quantifies over
   every `U : S.Etaleᵒᵖ`, `a : ULift.{u + 1} Γ(U.unop.left, ⊤)` and
   `e : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)`.
   Its equation is exactly F(ae) = a^p F(e). Pass. Both scalar and vector use the
   same lift. Lowering both, multiplying in the genuine section module, and
   lifting the result transports the scalar action along the lift bijection.
   I opened the additive universe-lift functor's source: it transports group
   operations and morphisms this same way. The explicit `@id` only pins the
   existing section type; it does not change a section or introduce a hidden let.
8. Coker(F-1) = 0: `IsZero (cokernel (F - 𝟙 _))`. Pass; a categorical zero
   object assertion in abelian sheaves, without any O_S-linearity requirement.
9. Ker(F-1) is constructible: `IsConstructibleAbelianSheaf (kernel (F - 𝟙 _))`.
   Pass. I opened ConstructibleAbelianSheaf.lean and LocallyClosedStratification.lean.
   The predicate gives one finite partition into constructible locally closed
   subschemes, with inverse images trivialized over étale covers by finite
   abelian groups. Thus every clause of the dependency's finite abelian stratum
   convention is present, including abelian (rather than set-only) isomorphisms.
10. No invertibility or globally constant rank: neither binder occurs. Pass.
    F is universally quantified after E, with semilinearity as its only extra
    condition, and both conclusions hold for this same F.

Edge cases: S may be empty; the definition permits n = 0 strata and the empty
partition. E may have rank zero on any chart or everywhere: F-1 is then an
endomorphism of the zero sheaf, with zero kernel and cokernel. F = 0 is allowed
and gives F-1 = -1. Variable rank on disconnected components is allowed by the
actual local-generator predicate. Nonreduced characteristic-p rings are allowed;
no reducedness or perfectness assumption was added. The base morphism forces
characteristic p in local rings, and no assertion is made for composite p or
characteristic zero. There is one arbitrary scheme universe u, with no independent
smaller test universe. The coefficient universe u+1 is the dependency's chosen
abelian-sheaf universe. Both lifts have that size, and all small étale objects
and their sections are tested. There is no external nonempty index restriction.

Independent H4 searches, using wording different from the worker's:

- LeanFinder: `Artin Schreier sequence finite locally free sheaf fixed sections
  constructibility`. Eight results, principally local-generator and cotangent
  declarations; none states either asserted sheaf conclusion for general F.
- Loogle: `"cokernel", "frobenius"`. No hits.
- msearch grep: `(ArtinSchreier|artinSchreier|semilinear).*(sheaf|Sheaf|kernel)`.
  No Mathlib hits.
- LeanSearch: `Fixed point sheaf of a p linear endomorphism on a vector bundle
  is constructible`. Service unavailable (HTTP internal server error); this is
  recorded as unavailable, not as evidence that no theorem exists.
- Independent rg on Mathlib, source WeilConjectures and project lean/Sheaf for
  Artin-Schreier/Frobenius with constructibility, kernel and cokernel found
  rank-one Artin-Schreier section results, a curve cohomology model, and
  constructibility of Artin-Schreier local systems. These do not state this
  general varying-rank semilinear fixed-point result. No matching theorem or
  duplicate definition was found.

There are no new definition nodes, dependency modules or statement corrections in
this delivery. All five dependency records supply exactly the notions needed.
I checked the recorded proof-dependency modules against the imports; the three
not-yet-stated proof nodes remain listed in the worker report. The docstring
contains the seven proof steps in order: affine matrices, polynomial étale solution
covers, fibrewise solvability and epimorphism, represented kernel, finite étale
strata, finite local abelian constancy, and global refinement. The source and
blueprint markers are present. There is exactly one named theorem, its whole
proof is `sorry`, and there are no definitions, private notation or local instances.

No mathematical or Lean mismatch was found. I changed only this report by adding
the independent second reading; the Lean and node metadata are retained. I checked
by exact string comparison that `lean.statement` equals the file's theorem
signature, and checked all lines are within 100 characters. All variables and the
single universe are explicitly bound. The required server scompile.py invocation
compiled the delivered module cleanly in 2.6 seconds (and its side-only dependency
ConstructibleAbelianSheaf in 1.6 seconds), nice 19, two threads, 60 seconds per file.
No local compiler or global build was run.
