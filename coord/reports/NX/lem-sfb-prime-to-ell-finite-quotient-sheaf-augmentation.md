## Worker report

The delivery states `Profinite.ContinuousScalarCochains.prime_to_ell_finite_quotient_sheaf_augmentation`
in `Sheaf.CategoryTheory.PrimeToEllFiniteQuotientSheafAugmentation`. Its only theorem has
proof `sorry`. `HasFiniteQuotientSheafAugmentation` is a fully written proposition specifying
the canonical objects in section coordinates; it makes no choice from the theorem.
This repair adds two existing-definition ownership nodes. There are no dependency-module repairs or statement corrections.

I read the node's full statement and all five proof steps, the four original statement
dependencies and their declaration docstrings/signatures, and the proof dependencies.
The source is latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). It gives the geometric
motivation; the finite-quotient sheaf argument is explicitly agent-formulated in the
node, with the external reference WANTED. The declaration docstring reproduces its five
steps, including the exact-equivalence transport inserted by stage-1 review.

Hypothesis and clause correspondence:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Norm-topological algebraic closure: `(Ω : Type u) [NormedField Ω]`
  `[NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]`. The normed algebra norm extends
  the padic norm. The finite intermediate field is `E : IntermediateField ℚ_[ell] Ω`
  with `[FiniteDimensional ℚ_[ell] E]`, using its inherited norm. The conclusion is the
  conjunction of the same predicate for `E` and `Ω`, exactly the two choices of F.
- Compact Hausdorff totally disconnected topological group: `Group K`, `TopologicalSpace K`,
  `IsTopologicalGroup K`, `CompactSpace K`, `T2Space K`, `TotallyDisconnectedSpace K`.
  `hK` quantifies over surjective continuous homomorphisms to finite discrete groups,
  with `Nat.Coprime (Nat.card Q) ell`. Such quotients have representatives in `Type u`
  because K does. Trivial action is built into the scalar differential; no coefficient
  action is introduced as extra data.
- The site is `coherentTopology Profinite.{u}`. The scalar object A is the recorded
  `Profinite.continuousMapRingObjOfUniverse.{u,u} F`, with its recorded `MonObj` and
  commutativity. Section lifts are in `u+1`; the ordinary module category is `Mod` on
  abelian sheaves. The standard localization uses morphism universe `u+2`.
- Nonnegative presheaf terms: `P : CochainComplex (Profiniteᵒᵖ ⥤ AddCommGrpCat) ℕ`.
  For each n,S, the additive map `e n S` is injective and has exactly the image
  `FactorsThroughFiniteQuotient`. This is the landed sibling's definition with one
  open normal subgroup and a continuous descended function on S times its quotient power.
  It allows unrestricted continuous dependence on S. The naturality equation states
  precisely pullback in S. Together with the scalar compatibility below, this is the
  A(S)-module of these functions, not a larger or smaller subspace.
- The differential equation uses the existing `scalarCochainDifferential n`.
  Its `Fin.contractNth` final face drops the last argument; the initial face drops
  the first. Thus its n+1 signed terms plus the first term are exactly the displayed
  inhomogeneous differential, including cancellation at n=0.
- `L : CochainComplex M ℕ` and the complex isomorphism `a` identify its underlying
  abelian complex with actual degreewise `presheafToSheaf` of P. `eta` is pinned by
  `toSheafify ≫ (sheafToPresheaf ...).map (a.hom.f n)`, not an arbitrary local map.
  The equation for r,p,q says the induced internal scalar action agrees with
  pointwise multiplication on every presheaf generator. These generators locally
  generate the sheafification, so the action is the unique sheafified A-module action.
  The existing section-module functor supplies this action, without reconstructing it.
- Degree zero: `z : Mod.regular A ≅ L.X 0`, and the equation involving `z.inv` and
  `e 0 S p` is its canonical identification with continuous scalar functions on S.
  `L.d 0 1 = 0`, `uL.f 0 = z.hom`, and `uL.f (n+1) = 0` fix the actual augmentation
  from `CochainComplex.single₀ M` of the regular module.
- Negative terms: `HomologicalComplex.extendMap ... ComplexShape.embeddingUpNat`
  extends both complexes by zero to the integers. No negative degree is omitted.
- Derived assertion: `IsIso (DerivedCategory.Q.map (extendMap uL ...))` is about this
  actual augmentation, not existence of an unrelated derived isomorphism.
- Image equals kernel in every positive degree: `∀ n, L.ExactAt (n+1)` in the internal
  A-module category, the ordinary abelian-category exactness condition.
- Every local cocycle: quantify n,S,x and require its actual sheaf differential to
  vanish. There is a covering sieve R; on every arrow f of R there are a presheaf
  section p, one open normal U, and continuous cbar through K/U. Its `eta` image is
  the restriction of x; the coordinate equality gives p=cbar pulled back, and
  `scalarCochainDifferential (n+1) cbar = 0` is the simultaneous cocycle equation.
  Quantification over `U0` and `U ≤ U0` expresses that the same cover/quotient can be
  refined simultaneously with any prescribed initial quotient, by intersection.
- Each such representative, not just one chosen representative: the separate universal
  cbar clause ranges over every S,U,cbar cocycle. It produces continuous bbar on the
  same quotient and p-degree-n element b, with e(b) its quotient pullback. The formula
  is `(-1 : F)^(n+1) * (Nat.card ... : F)⁻¹ * ∑' h, cbar (s, Fin.snoc g h)`.
  Here the statement's positive degree is n+1. The quotient is finite by compactness
  and openness, so `tsum` is the finite sum, without an enumeration choice.
  The next equation is `scalarCochainDifferential n bbar = cbar`.
  Compatibility of the complex isomorphism a and of eta then makes its sheaf image
  the local primitive of x. The additional `n = 0 → cbar = 0` is exactly the node's
  degree-one vanishing clause.
- Empty test objects are allowed throughout. K=1 is allowed. There is no `Nonempty S`,
  `CompleteSpace Ω`, completed coefficient field, infinite averaging operation, or
  restriction of the range to a finite subextension. Finite `tsum` does not impose
  completeness or summability assumptions.

Dependency declarations used:

1. `Sheaf.Topology.ContinuousMapCondensedRing`: the recorded continuous-map ring
   presheaf/sheaf, underlying abelian sheaf, monoid structure and commutativity.
2. `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its morphisms,
   `Mod.forget`, `Mod.regular`. This is the recorded internal module convention.
3. `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
   derived convention module, imported transitively through the landed sibling;
   the actual derived-category declarations are `DerivedCategory`, `HasDerivedCategory.standard`,
   `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
4. The size-convention dependency is metatheoretic; explicit `u`, section universe
   `u+1`, and localization universe `u+2` implement it.
5. New existing-definition statement dependency `def-sfb-finite-quotient-scalar-cochains`:
   module `Sheaf.CategoryTheory.PrimeToEllCochainFiniteQuotientDescent`, declaration
   `Profinite.ContinuousScalarCochains.FactorsThroughFiniteQuotient`. Its theorem
   is not used to define or choose our complex; only its existing factorization notion
   is reused. In particular there is no downstream dependency wait.
6. Added landed statement dependency `def-weil-pbc-internal-abelian-sheaf-module-equivalence`:
   module `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, declarations
   `CategoryTheory.InternalAbelianSheafModule.sectionRings`, `sectionModuleFunctor`,
   `sectionModuleEquivalence`. The proof already cites this node; its section action
   is also needed to write the statement.
7. New existing-definition statement dependency `def-sfb-parametrized-scalar-cochain-differential`:
   module `Sheaf.Analysis.ScalarCochainAveragingPrimitives`, existing
   `WeilConjectures.scalarCochainDifferential`; its theorem is a proof dependency.
8. Proof-only imports: `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
   (`CategoryTheory.sheafification_sections_local`),
   `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` (recorded sheafification
   interface and exactness leaves), and `Mathlib.CategoryTheory.Sites.PreservesSheafification`
   (`sheafifyComposeIso` and its unit compatibility, recorded underlying-set leaf).
   These prepare exactly the node's proof dependencies, as required by stage 2.

Searches actually run with msearch.py for this item:

- LeanFinder: "Sheafified finite quotient continuous scalar cochains have a canonical
  quasi isomorphic scalar augmentation and finite averaging primitives". Eight hits,
  including homogeneous continuous cochains and abstract standard resolution, but none
  is this finite-quotient sheaf augmentation with local signed primitives.
- Loogle: "groupCohomology, ContinuousMap". Zero hits.
- LeanSearch: "Finite quotient continuous scalar cochain presheaf sheafification
  augmentation quasi-isomorphism". Eight hits, chiefly general module sheafification,
  its adjunction and unit. Used the existing general interfaces, no theorem match.
- Mathlib grep: `finiteQuotient.*[Cc]ochain|finite_quotient.*cochain|[Cc]ochain.*[Aa]verag`.
  Zero hits.
- Project/upstream rg: finiteQuotient/finite_quotient/FiniteQuotient and scalar-cochain
  names, then the exact proposed declaration names, in `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`. Found the sibling coordinate
  predicate and the scalar differential, both reused. Other finite quotient hits
  concern coefficient reduction, not the present complex or augmentation.
- Upstream grep for the exact item id: no hits.
- `tools/blueprint_refs.py search 'finite quotient cochain'`: zero blueprint nodes.
- DAG sibling record and full Lean module were read to avoid duplicating its predicate.

Edge cases checked before finalizing: n=0 gives degree-one zero from the cancelling
scalar differential; n=1 gives the positive sign in degree two; n=2 gives the negative
sign in degree three. Degree zero identifies K^0 with a singleton. For K=1 the positive
differentials alternate identity and zero; this agrees with ExactAt. Empty S has only
zero continuous maps, and every quantified formula remains valid. For a local
representative p the binder must be over S', not S: this was corrected before the first
compile, so a general sheaf section is never required to have a global representative.
For an arbitrary initial U0, intersection with the representative's quotient gives
U≤U0 without changing the represented section or its cocycle equation.

Validation: prescribed scompile.py compiled both the sandbox and library-shaped module
on the server successfully (10.9 s and 3.9 s), no errors or warnings. All variables are
explicit (`set_option autoImplicit false`), all lines are at most 91 characters, and the
only postponed proof is the named theorem matching the assigned DAG node.

## Second reading by NX

This is the dispatcher's requested worker self-check; no second agent was started.
The maintainer supplies the independent review after delivery.

With the node and final file open, I checked every binder and all clauses above again.
The module uses the same normed Ω/E hypotheses and finite discrete quotient condition
as the already landed sibling. The finite-quotient image is neither all continuous
cochains nor locally constant S-dependence. The scalar equation is on eta-images for
all r and p,q, so the internal action is fixed, not merely an abelian sheaf structure.
The complex isomorphism a fixes the differential after sheafification. The z equation
normalizes the regular scalar module at degree zero, hence uL is its actual identity
there; the statement uses IsIso of Q.map of precisely uL extended to ℤ.

I checked that local representatives live on S' and are only required on the covering
sieve, while both their representative equation and finite-quotient cocycle equation
hold on that same S' and U. The primitive clause is universal over every representative
and pins its sign, denominator, last coordinate and db=c identity; n=0 explicitly forces
the original degree-one cocycle to be zero. Positive image-kernel exactness is internal,
and the negative terms are handled by extension by zero. The expression `@id` only
exposes the existing section-module action's carrier; it is not a cast changing data.
No additional discrepancy was found, and no statement correction is needed.


## Returned delivery repair

The single return at immutable head `1e687f985aea` (H4/H12) is repaired: removed
`lem-sfb-prime-to-ell-cochain-finite-quotient-descent` and
`lem-sfb-scalar-cochain-averaging-primitives` from statement dependencies. Added
`def-sfb-finite-quotient-scalar-cochains` and
`def-sfb-parametrized-scalar-cochain-differential`, each binding the existing plain
definition by an `existing: true` record. The scalar averaging theorem remains in proof dependencies, where step 3 cites it.
The descent theorem is absent from proof dependencies because no proof step uses it.
The two definitions are exported by different source modules, so two independently
checkable existing-definition records implement the requested ownership repair.
The item's Lean source, signature, hypotheses and all clauses are unchanged. The
current main node differs from the returned sandbox only in its absent lean record
and original statement dependencies; the repaired node is regenerated from that
current main node, retaining its other metadata and proof. Delivery wrappers build
the repaired commit against refreshed current main, not against the returned branch.

## New nodes

`def-sfb-finite-quotient-scalar-cochains` owns the existing
`Profinite.ContinuousScalarCochains.FactorsThroughFiniteQuotient` in
`Sheaf.CategoryTheory.PrimeToEllCochainFiniteQuotientDescent` (line 49). It defines
factorization through one open normal quotient with continuous unrestricted parameter
dependence. Its statement does not claim finiteness for a noncompact K; compactness
is exactly when openness makes the quotient finite. Source: the assigned node's
explicit finite-quotient definition in the agent expansion of latest paragraph (3).
The signature and body were read again; no theorem is used by the definition.

`def-sfb-parametrized-scalar-cochain-differential` owns the existing
`WeilConjectures.scalarCochainDifferential` in
`Sheaf.Analysis.ScalarCochainAveragingPrimitives` (line 35). Its self-contained statement
is the coordinate differential for any parameter set, group and ring; it includes the
last face and degree-zero cancellation. Source: the assigned node's displayed
differential in the same agent expansion. No continuity or norm assumption is added
to the formula. It is distinct from def-sfb-continuous-inhomogeneous-cochains, whose
interface includes a topological representation, a nontrivial first-face action and
a continuous linear differential/complex; this node records the existing plain
parametrized formula used here.

For both nodes, fresh logged searches were run for this repair: LeanSearch query
"Parametrized trivial scalar cochain differential and continuous cochains factoring
through an open normal finite group quotient" returned eight related group-cohomology
hits; Loogle query "scalarCochainDifferential, FactorsThroughFiniteQuotient" returned
zero hits and unknown identifier scalarCochainDifferential; Mathlib grep for the two
exact names returned zero hits. Project rg found precisely the two declarations above
and no upstream WeilConjectures definitions. DAG definition searches found no ownership
node for these exact interfaces. Whole-blueprint searches "finite quotient scalar
cochains" and "parametrized scalar cochain differential" each returned zero matches.
`blueprint_refs.py ancestor` confirmed inherited null ancestor for this item; the
new nodes retain that null and prepend this item to its via chain. Every recorded
mathlib_searches entry copies the actual repair search-log result.

Repair self-reading: each new node's statement was compared with its full existing
signature and real definition body. Empty S, n=0, arbitrary topological F, and
noncompact K are allowed by the factorization predicate; the quotient is only called
finite under compactness. The differential permits an arbitrary ring and no topology,
has d0=0, and has the same signs as the unchanged item. Neither definition calls the
source theorem. These nodes contain no theorem dependencies. Independent review of
all other mathematical clauses at returned head 1e687f985aea is preserved.


## Repair of returned head 25bb6ace8586

The single review_split.py finding is repaired: removed
`lem-sfb-prime-to-ell-cochain-finite-quotient-descent` from `proof_deps`. It had been
added during the previous ownership repair but is not used by any of the five proof
steps. Its plain factorization definition is still supplied by the new existing:true
`def-sfb-finite-quotient-scalar-cochains`; the descent theorem is unnecessary here.
The averaging theorem remains a proof dependency and is explicitly cited by step 3.

I compared the current main node with the returned sandbox. The proof steps and
statement are identical; the repaired proof_deps now equal both the current main list
and the exact union of uses of the five steps. No proof step, Lean declaration,
statement dependency or existing-definition ownership record changed in this repair.
The earlier report's claim that both theorem nodes were retained as proof dependencies
is corrected above. This is a substantive metadata repair of the returned packet.
