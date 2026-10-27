## Worker report

Stage 2, group NM, item `lem-trf-finite-normalization-quotient-local-criterion`.
The earlier unchanged-item ending concerned the stage-1 split. The current live item
has a reviewed split and no Lean record. This delivery adds its Lean statement; it
preserves the accepted statement and proof. This packet repairs the independent
review return on immutable head 763a646cc82c (H2/H12).

The module `Sheaf.AlgebraicGeometry.FiniteNormalizationQuotientLocalCriterion`
states `AlgebraicGeometry.finite_normalization_quotient_local_criterion`, with one
whole-proof `sorry` and no new Lean definitions; the repair adds an existing-definition
ownership node. The source read is Stacks Morphisms
`lemma-description-normalization` (035P) and `lemma-stalk-normalization` (0C3B),
`literature/stacks-project/morphisms.tex`, lines 14426–14504. For reduced schemes
0C3B's reduced local ring is the local ring itself. The coherence and quotient
conclusions are the deductions in the item's five accepted proof steps, copied
as a natural-language proof in the declaration docstring.

Hypotheses and clauses, against the node and the actual Lean signature:

- An arbitrary scheme is `(X : Scheme.{u})`; `u` is declared explicitly. No base
  field, finite-type-over-a-field, dimension, connectedness, global Noetherianity
  or nonemptiness hypothesis is imposed.
- Reduced and locally Noetherian are `[IsReduced X] [IsLocallyNoetherian X]`.
- The morphism is exactly `X.fromReducedNormalization`, with source
  `X.reducedNormalization`, not a relative normalization of an arbitrary map.
  Its finiteness is `[IsFinite X.fromReducedNormalization]`.
- `C_X` is the existing `conductorCokernel X`, definitionally the cokernel of
  `SheafOfModules.unitToPushforwardObjUnit
  X.fromReducedNormalization.toRingCatSheafHom`. No replacement cokernel object
  is introduced. `ShortComplex.cokernelSequence` of that very arrow, followed
  by `.ShortExact`, renders the displayed sequence, including injectivity and
  surjectivity at its ends.
- `RingedSpace.IsCoherent X.toRingedSpace` is asserted of the pushforward of the
  structure module and of `conductorCokernel X`. This is the finite-type and
  finite-type-kernel definition, not merely a quasi-coherence condition.
- Every affine open is quantified as `(U : X.Opens) (hU : IsAffineOpen U)`.
  Its ring `A` is `Γ(X, U)`. The sections of
  `(Scheme.Modules.pushforward X.fromReducedNormalization).obj
  (SheafOfModules.unit X.reducedNormalization.ringCatSheaf)` over `U` are `B`:
  definitionally the sections of the normalization over the inverse image.
- `Function.Injective (X.fromReducedNormalization.app U).hom` says the actual
  structural ring homomorphism identifies `A` with its image subring in `B`.
- `B/A` is the module quotient by the linear range of the structural arrow on
  `U`. This uses the sheaf module's own canonical scalar action. The
  `Module.Finite Γ(X, U)` clause asserts that this quotient is finite.
- The linear equivalence `e : B/A ≃ₗ[A] Γ(conductorCokernel X, U)` is specified
  on every representative by `e (range.mkQ s) = (cokernel.π ...).val.app (op U) s`.
  Thus it identifies the canonical quotient maps, rather than only asserting
  that the two modules happen to be isomorphic.
- The isomorphism `E : tilde (ModuleCat.of A (B/A)) ≅
  (conductorCokernel X).restrict hU.fromSpec` is the sheaf comparison on the
  canonical chart `Spec Γ(X,U)`. Its top-section formula sends `tilde.toOpen`
  of `q` to `e q`, transported by the actual restriction adjunction unit and
  `hU.fromSpec_preimage_self`. These are the canonical section identifications.
  A morphism from tilde is determined by these global sections under its
  adjunction, so this formula fixes the comparison as well as its existence.
- For every `x : X`, `R` is `X.presheaf.stalk x` and the total fraction ring is
  Mathlib's `FractionRing R`, its localization at all non-zero-divisors; `R`
  is not assumed to be a domain in this clause.
- The numerator is the existing `X.normalizationPushforwardStalk x`, the ring
  stalk of the actual direct-image structure presheaf. The algebra equivalence
  `e : ... ≃ₐ[R] integralClosure R (FractionRing R)` preserves the structural
  inclusion of `R`, as required by 0C3B.
- The second `E` identifies the actual module stalk of `conductorCokernel X`
  with `integralClosure R (FractionRing R)` modulo the range of
  `Algebra.linearMap R ...`. Its formula on germs of all local sections `s`
  of the normalization says that the stalk quotient map corresponds to taking
  the class of `e (germ s)`. This specifies the canonical quotient isomorphism,
  rather than an unrelated linear equivalence.
- The final clause is `Subsingleton ((RingedSpace.moduleStalkFunctor ...).obj
  (conductorCokernel X)) ↔ IsDomain R ∧ IsIntegrallyClosed R`. Subsingleton
  is precisely vanishing of this module; the conjunction on the right is the
  recorded normal-domain notion. No domain hypothesis is assumed prematurely.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`,
  sectionwise definition, and the reduced-stalk instance.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  with its every-affine-open Noetherian field.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`:
  `AlgebraicGeometry.Scheme.reducedNormalizationComponent`,
  `isIntegral_reducedNormalizationComponent`, `reducedNormalization`,
  `fromReducedNormalization`; the data are the coproduct of the integral
  reduced components' function-field normalizations and its canonical map.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  affine plus finite affine section maps.
- `Sheaf.TraceFormula.ConductorSmoothBaseChange`:
  `AlgebraicGeometry.conductorCokernel`, its exact existing cokernel definition.
- `WeilConjectures.AlgebraicGeometry.Coherent`:
  `AlgebraicGeometry.RingedSpace.IsCoherent`. This is the `closed` upstream
  declaration in `pqf-def-coherent.lean_audit.slopmaster2.decls`. The node's
  more recent primary record `IsQuasiCoherentFiniteType` alone does not express
  its coherent clause; the closed upstream declaration in the same node does.
  We use that exact declaration, with no duplicate definition or record repair.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  `IsDomain R ∧ IsIntegrallyClosed R` follows the recorded inline convention.
- `Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper`:
  `AlgebraicGeometry.Scheme.normalizationPushforwardStalk` and
  `normalizationPushforwardStalkAlgebra`. These are unconditional definitions
  on every scheme, despite the curve theorem in their owning module. The
  definition node `def-trf-normalization-pushforward-stalk` records both existing
  declarations and is added to `stmt_deps`. The theorem node
  `lem-trf-normalization-singular-skyscraper` is removed from `stmt_deps`: its
  theorem is not used. The import stays because it supplies these definitions.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.toOpen`, and its
  adjunction characterization; `Mathlib.AlgebraicGeometry.Modules.Sheaf`:
  restriction and `Scheme.Modules.restrictAdjunction`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` on the existing sheaf modules.

Available proof-dependency modules are imported without `public`; public imports
supply the displayed statement interfaces. The two statement-only proof prerequisites
`lem-sfb-normalization-affine-total-fractions` and
`lem-trf-total-fractions-prime-localization` have no recorded declarations yet,
so there is no module for them to import. They are named in the proof docstring.
Mathlib leaves are supplied by Noetherian, Tilde, Localization.Integral,
Localization.Submodule and Ideal.MinimalPrime.Noetherian. No independent missing
notion is needed and no postponed helper theorem is introduced.

Edge cases checked mathematically:

- Empty `X`: no points, empty component coproduct; all stalk clauses are vacuous.
  The empty affine open is allowed. Its rings, finite quotient, and tilde module
  are zero; injectivity is the map between singleton rings. There is no
  nontrivial-ring binder on an affine chart.
- A normal local domain: the numerator equals `R`, the quotient is zero, and
  the criterion has both sides true.
- `k[x,y]/(xy)` localized at the origin: the local ring is reduced with two
  branches, the integral closure is a product, and the quotient is nonzero.
  The theorem permits the numerator and total fractions to have zero-divisors;
  its final domain conclusion occurs only inside the equivalence.
- A cusp local ring: the ring is a domain but not integrally closed, so the
  nonzero quotient prevents the mistaken domain-only criterion.
- Arbitrary characteristic, infinitely many global components and a locally
  Noetherian scheme that is not quasi-compact are allowed. All finiteness of
  components needed in the proof is on affine or quasi-compact opens.
- Each isomorphism's normalization equation is checked at the actual quotient
  projection; no arbitrary choice of scalar action or map is a hypothesis.

Searches actually run on this attempt (2026-10-23):

- `msearch.py ... leanfinder`: “For finite normalization of a reduced locally
  Noetherian scheme the normalization quotient is coherent and its stalk
  vanishes exactly at normal local rings”. Eight hits, including Mathlib's
  relative normalization, normalizationDiagram and reduced/integral instances;
  none states this componentwise quotient theorem.
- `msearch.py ... loogle`:
  `AlgebraicGeometry.Scheme.Hom.normalization, IsIntegrallyClosed`: zero hits.
- `msearch.py ... grep`:
  `normalization.*cokernel|normalization.*stalk|conductorCokernel`: zero Mathlib hits.
- `msearch.py ... leansearch`: “For a reduced locally Noetherian scheme with
  finite normalization the coherent normalization cokernel has stalk integral
  closure modulo the local ring and vanishes precisely at normal local rings”.
  Eight hits: relative normalization declarations and
  `IsIntegralClosure.isNoetherian`; none is the node's statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for normalization and
  stalk/quotient/cokernel names, and literal item-id grep: no existing exact
  theorem. `NormalizationSingularSkyscraper` supplies the reusable ring stalk
  and scalar action; its theorem has curve and algebraically closed field
  hypotheses and cannot serve as an existing match. `NormalizationMonoProperties`
  concerns étale constant sheaves, a different quotient. The conductor theorem
  assumes finite type over `ℚ`, so it is not this general statement either.
- `dag/lean_names_upstream.json` and source name search for
  `finite_normalization_quotient_local_criterion`: no collision.

Validation: `scompile.py NM lem-trf-finite-normalization-quotient-local-criterion
lean/Sheaf/AlgebraicGeometry/FiniteNormalizationQuotientLocalCriterion.lean` passed
in module mode, both sandbox and library-name checks. Initial errors in inferred
quotient projection types and `.app` syntax were repaired by spelling out the
linear range and using `.val.app (op U)`. All variables and universes are explicit;
there is no `let`, file-local notation, auxiliary axiom or data `sorry`.
No statement correction or unresolved statement dispute is needed.

## Second reading by NM

Author's second pass, not an independent review; the dispatched brief assigns the
independent reading to the maintainer and forbids starting other agents.

I reopened the node and the completed signature. Its hypothesis list has exactly
reducedness, local Noetherianity and finiteness of the specified componentwise
normalization. The first three conjuncts are the actual cokernel short exact
sequence and the two coherent objects. The affine clause ranges over every affine
open, uses the structural injection and the range quotient, asserts finiteness,
and provides the section and tilde comparisons with their canonical top-section
formula. The stalk clause uses the ring stalk of the pushforward, algebraically
identifies it with the integral closure in the full total fractions, and identifies
the actual cokernel stalk with its quotient, with a formula on every germ.
The last equivalence includes both being a domain and being integrally closed.

This pass removed a redundant explicit `Module.Finite A B` conjunct: it already
follows from the finiteness hypothesis, while the node explicitly asks for the
finite quotient module. No hypothesis or clause was weakened. I checked that the
quotient scalar action is the structural one, that an algebra equivalence preserves
`R`, that the affine restriction formula uses the canonical fromSpec chart, and
that the existing unconditional stalk definition adds no curve hypotheses.
All theorem proofs in the new file are the single expected whole-proof `sorry`.

## New nodes

`def-trf-normalization-pushforward-stalk` owns the already landed
`AlgebraicGeometry.Scheme.normalizationPushforwardStalk` and
`AlgebraicGeometry.Scheme.normalizationPushforwardStalkAlgebra`, recorded with
`existing: true` on `Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper`.
The first is exactly the direct-image ring stalk; the second is the algebra
structure from the stalk of the canonical structure-sheaf map. Source: Stacks
0C3B, `lemma-stalk-normalization`, item (1) and its local-ring algebra structure.
Both definitions bind only `X : Scheme.{u}` and `x : X`, with no reducedness,
Noetherianity, curve, field or finiteness assumptions. On the empty scheme the
point binder has no instances. No data are chosen and no new Lean code is needed.

Repair searches (2026-10-23): LeanSearch for the stalk of the pushforward of the
componentwise reduced normalization returned eight generic stalk/affine-spectrum
algebra declarations. LeanFinder for the local-ring algebra structure returned
eight relative-normalization/function-field/affine stalk declarations. Neither
is this existing specialization. Mathlib grep
`normalizationPushforwardStalk|normalization.*[Ss]talk` returned zero hits.
`rg` of WeilConjectures and Sheaf found the two definitions only in
NormalizationSingularSkyscraper. DAG grep found only the theorem node carrying
these names, and blueprint_refs search found zero blueprint nodes. The actual
queries and returned hits are recorded in the new node and searches.jsonl.
Thus the new node records the existing definitions rather than duplicating them.

## Repair of return H2/H12

The saved packet first passed the required dry run at ee712f508fc, but still
contained the defect named by the independent return at 763a646cc82c. The item
now cites `def-trf-normalization-pushforward-stalk` instead of the theorem node
`lem-trf-normalization-singular-skyscraper`. The new node's only dependencies
are the scheme and componentwise normalization definitions, both already in
the item's dependency ancestry, so the substitution creates no cycle. The
Lean module, its theorem signature, the node's mathematical statement and
proof are unchanged. The item's lean.note now also explicitly identifies
upstream `RingedSpace.IsCoherent` for `pqf-def-coherent`, as advised.

Second reading of the repair by NM (author self-check; no agents permitted):
I reopened both existing definitions and compared their bodies with the new
node. The abbreviation is literally the stalk of the direct-image structure
presheaf, and the instance is literally the algebra of the stalk map; its
source and target are the stated rings. The signature is copied verbatim.
I compared the saved node with current main: only lean and the permitted
additional definition stmt_dep differ. Every theorem clause reviewed in the
original immutable head is retained byte for byte. No dependency module or
statement correction is introduced.

Repair validation: explicit scompile.py passed both sandbox (6.4 s) and
library-name (3.7 s) compilation with no diagnostics.
The repaired dry run requested the standard empty import_flags field on the
new node; it is supplied as import_flags: [].


## Repair of reachability return at 9a79a46ba3ab

The retained packet first passed the prescribed dry run (4a0a52f4fe8), but
independent incremental DAG validation found that the new ownership node
`def-trf-normalization-pushforward-stalk` is outside the target reach and has
no `unreachable` flag. The item belongs to the historical conductor refinement;
its citing the new definition does not make that refinement a target ancestor.
The new node now carries `import_flags: ["unreachable"]`, following the exact
return and the reachability contract in tools/check_dag.py. No mathematical
statement, Lean declaration, dependency edge, or existing node field is changed
by this repair. The saved module and the item's Lean record are retained.

Self-check by NM: reopened both node files and the theorem module, compared the
item with current main (only lean and the added definition stmt_dep differ), and
reopened normalizationPushforwardStalk and normalizationPushforwardStalkAlgebra
in their existing source. The abbreviation is the actual pushforward ring stalk;
the instance is induced by the structural stalk map. The new node is cited by
the item; it has no theorem dependency and introduces no cycle. The sole return
is addressed by the new node's reachability flag, without changing any signature.

Repair validation: prescribed scompile.py passed sandbox and library-name
compilation (7.6 s and 7.4 s), with no diagnostics. The repaired packet passed
deliver2.py --no-push at 9fc97f6ac2f: preflight and per-file compile both OK.
