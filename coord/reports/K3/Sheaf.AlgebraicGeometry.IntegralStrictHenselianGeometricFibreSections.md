## What changed

Proved `AlgebraicGeometry.Etale.isIso_integralStrictHenselianGeometricFibreRestriction`
with its original signature and visibility. Added three proved private helpers:
`isIso_sections_of_bijective_set_unit`, `integral_connected_inter`, and
`isIso_integral_henselianRestriction`. The first helper is generalized to an arbitrary morphism of schemes with bijective
set-valued adjunction unit at the identity object. It imposes no field-extension or
separably-closed-base assumptions. The main proof supplies that hypothesis by applying
`AlgebraicGeometry.etale_sections_base_field_extension` from the existing public module
`Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension`. The duplicate private theorem
`isIso_sections_fieldExtension` has been removed, as requested in the returned delivery.
The proper-fibre module is unchanged.
The main proof factors the closed geometric point through the residue field, composes the
ordinary-fibre and field-extension restrictions, and changes Cartesian models canonically.

The integral henselian comparison is proved directly by the finite-cover connectedness
criterion. In each finite cover, the affine spectrum homeomorphism identifies the relevant
intersection with V(P + IB). Added proof-only imports of
`Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion`,
`Sheaf.RingTheory.HenselianPairPrimeConnected`,
`WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`, and
`WeilConjectures.SixFunctors.BaseChange.GlobalSections`. Updated the item's DAG proof and
proof dependencies to match this route. No public imports, definitions or statements changed.
No modules held by other groups were adapted. No new modules or nodes.

Sources read: [09XK](https://stacks.math.columbia.edu/tag/09XK),
[09Y6](https://stacks.math.columbia.edu/tag/09Y6),
[09ZF](https://stacks.math.columbia.edu/tag/09ZF), and
[0A3I](https://stacks.math.columbia.edu/tag/0A3I).
Searches: LeanFinder returned eight local-map/etale-locus results, no section theorem;
Loogle `HenselianRing` returned the predicate, maximal-ideal instance and basic constructors;
msearch grep `henselian.*section|isConnected.*zeroLocus` returned no Mathlib match.
Local rg found the existing proper geometric-fibre proof and canonical composition formulas.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.isIso_integralStrictHenselianGeometricFibreRestriction`
(node `lem-sbc-integral-strict-henselian-geometric-fibre-sections`).
One of one original sorries proved from existing library declarations; zero split off,
zero new sorries. Every private helper is proved. No sorry remains in this delivery.
This is a proof from library dependencies, not a claim that every dependency is axiom-free;
the delivery tool's probe checks the remaining transitive dependency status.

The proof handles empty integral schemes (there is then no irreducible C to test),
zero coefficient rings, and arbitrary field extensions, including transcendental ones.
No arbitrary data is chosen from an unproved existence theorem. The algebra structure on
B is the actual global-sections ring map and the residue lift is canonical.

## No longer needed

Removed the proof-only import
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero`.
Pruned dependency `lemma-weil-pbc-etale-degree-zero` from this item's DAG route.
The proper identity comparison, Stein factorization for proper schemes, and proper henselian
connectedness are unnecessary for this proof. In particular the proof no longer imports
`WeilConjectures.AlgebraicGeometry.HenselianConnectedness` or
`Sheaf.AlgebraicGeometry.SteinFactorizationAffine` through DegreeZero.
The elementary canonical Stein-base identity from GammaSpecAdjunction remains in use;
no theorem about proper Stein factorization is used.
All remaining proof imports are used explicitly. Other target routes may still require
these pruned modules; this report only asserts their removal from this item's route.

## Where the brief, the DAG or earlier work was wrong

The planned application of the proper degree-zero theorem to the identity of Spec B is
valid but unnecessary. The existing finite-cover criterion and prime connectedness theorem
give a direct argument that avoids a separate quotient-spectrum pullback identification.
The original theorem docstring describes the earlier valid route; the delivered DAG proof
and the private helper comments describe the actual route. No existing library statement was disputed or changed. The return correctly identified
that the previous delivery duplicated the private field-extension theorem from
`ProperStrictLocalFibreSections`. That theorem cannot be imported because it is private.
This repair uses the permitted generalization option: the local helper now handles
any scheme morphism, and the field-specific premise is proved at its use by the existing
public set-section theorem. This is a substantive generalization of the proof, rather
than a renamed duplicate or a whitespace change. The local literature source checkout is absent; the cited source tags were read
on the Stacks website instead. The unit realization record has no required realized steps
at this node, and the integral comparison in the unit's route is retained.


Validation of the repair: the item compiles cleanly with `lcompile.py`.
The previous second-reading record was removed because it predates this repair;
the independent second reader must review the repaired delivery.

## Second reading by K3

1. **Interface: pass.** Diffed the sole delivered Lean module against the repository.
   The complete signature and visibility of
   `AlgebraicGeometry.Etale.isIso_integralStrictHenselianGeometricFibreRestriction`
   are byte-for-byte identical. In particular Λ remains any commutative ring, A
   strictly henselian local, p integral without finiteness or properness, Ω an
   arbitrary algebraically closed field, ht the closed-point condition, sq the
   supplied Cartesian square, and F any étale module sheaf. There is no definition
   change, public-import change, adaptation, or change record needed.
2. **Proof: pass.** Compiled the module cleanly with lcompile.py. A scratch copy
   printed axioms for the public theorem and all three private helpers. The
   general set-unit transfer and integral connected-intersection helpers use only
   propext, Classical.choice, and Quot.sound. The henselian restriction helper and
   public theorem additionally depend on inherited sorryAx; no additional axiom
   occurs. No sorry, axiom, unsafe, opaque, implemented_by, or extern occurs in the
   delivered source. Γ(X,⊤), its actual induced ring map, the affine isomorphism,
   the unique residue-field lift, and canonical pullbacks construct all data;
   no arbitrary witness is selected from an unproved existence theorem.
3. **Split statements and search: pass.** No statement is split off and no new
   node is added. Read the three proved private helpers and the existing public
   dependency statements. The set-unit transfer has genuinely general hypotheses
   on an arbitrary scheme morphism, unlike the private field-specific theorem in
   ProperStrictLocalFibreSections. Its use supplies the premise from the existing
   public etale_sections_base_field_extension. Independent rg searches for
   isIso_sections, henselianRestriction, finite_connected_closed_intersections,
   and globalSectionsUpperStarMap_comp found the already used public criterion
   and composition formula, and the inaccessible private field-specific helper.
   msearch grep for IsIso.*globalSections|Bijective.*unit|henselian.*restriction
   found no exact Mathlib theorem replacing the assembled argument. Edge cases:
   the zero integral algebra has empty spectrum and no irreducible C; irreducible
   C is nonempty and gives a prime P; henselian Jacobson containment guarantees
   V(P+IB) nonempty as well as connected. Zero coefficients cause no exception.
   The field-extension step assumes no algebraicity of Ω over the residue field.
4. **Route and pruning: pass.** Checked the argument top downward: first the
   henselian ordinary fibre, then the separably closed field-extension comparison,
   then the canonical composition and pullback isomorphisms. Each proof-only
   import supplies an explicitly used declaration; the three original public
   imports supply signature notions. The old proof_deps minus the new list is
   exactly lemma-weil-pbc-etale-degree-zero, already listed under No longer needed
   with its DegreeZero module. Read dag/units/sk-lem-universal-datum.json:
   realized.statement is [] and realized.steps is [[]], so no required realized
   node step is bypassed. The integral comparison used by that unit stays intact.
5. **DAG: pass.** Diffed the node: only proof, proof_deps, and proof_origin changed.
   Checked every dependency's Lean declaration. The union of proof-step uses is
   exactly proof_deps: integral henselian transfer, prime connectedness, the finite
   connected criterion, set sections after field extension, module/set comparison,
   and global-section composition. These match the actual Lean calls. No new-node
   fields are required.

Second reading changed only this report, adding the independent checks and axiom
qualification; no proof repair was needed. The existing theorem docstring describes
an older valid proof route. Suggested replacement for its ordinary-fibre paragraph:
use the affine identification of irreducible closed subsets with V(P), henselian
connectedness of V(P+IB), and the finite-cover criterion to obtain invertibility.
The delivered DAG and helper comments already describe this actual route; the
existing docstring is preserved under the Lean skill's existing-docstring policy.
