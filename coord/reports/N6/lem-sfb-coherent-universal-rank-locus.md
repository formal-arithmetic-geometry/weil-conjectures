## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentUniversalRankLocus` states
`AlgebraicGeometry.Scheme.Modules.exists_coherentUniversalRankLocus`, with its
proof `by sorry`. It follows the current, already accepted Q59 split, including
all nine proof steps in the declaration docstring. No statement correction is
needed. No other theorem or definition is introduced.

Clause-by-clause correspondence:

- `S : Scheme.{u}` is the base scheme. `[IsLocallyNoetherian S]` and
  `[CompactSpace S]` are exactly the two parts of Noetherianity specified in
  the node. No separatedness assumption is made.
- `F : S.Modules` is an actual sheaf of structure-sheaf modules;
  `hF : RingedSpace.IsCoherent S.toRingedSpace F` is coherence as Stacks 01BV,
  including finite type and finite-type kernels of all finite-free local maps.
  On the locally Noetherian base this is equivalent to the landed
  `IsQuasiCoherentFiniteType` predicate by
  `Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`. The item
  records this in `lean.note`; the dependency record is retained unchanged.
  There are no extra quasi-coherence or finite-presentation hypotheses.
- `r : ℕ` is the nonnegative integer, including zero.
- `S.residueField s` is the recorded residue field κ(s), and
  `(S.residue s).hom` is the canonical quotient O_{S,s} → κ(s).
  `(RingedSpace.moduleStalkFunctor S.toRingedSpace s).obj F` is the recorded
  module stalk with its canonical O_{S,s}-module structure. Applying
  `ModuleCat.extendScalars (S.residue s).hom` constructs
  κ(s) tensor_{O_{S,s}} F_s, with the quotient map supplying the scalar
  action explicitly. This is canonically the tensor in the node, with its
  two factors interchanged. It is a real Mathlib tensor construction, not
  an arbitrary vector space or an assumed comparison map.
- `Module.finrank (S.residueField s) (...) ≤ r` is the precise fibre-dimension
  bound. Coherence on a locally Noetherian scheme implies the stalk is
  finite, so this residue vector space is finite dimensional; the convention
  that finrank of an infinite-dimensional space is zero is never used.
- `∃ W : S.Opens, (∀ s, s ∈ W ↔ ...) ∧ ...` asserts openness of exactly
  W_r(F), with its canonical open-subscheme structure. Neither only one
  inclusion nor a possibly larger open neighbourhood is asserted.
- `∃ I : W.toScheme.IdealSheafData, ...` supplies a quasi-coherent ideal
  on W. Its closed subscheme is the existing canonical `I.subscheme` and
  its inclusion is `I.subschemeι`. Mathlib supplies
  `IsClosedImmersion I.subschemeι` and `I.subschemeι.ker = I`; consequently
  using these objects directly includes both the closed-immersion clause
  and the requirement that it be cut out by I. No additional existential
  scheme or arbitrary closed immersion can detach C from its ideal.
- For every `T : Scheme.{u}` and `g : T ⟶ S`, the biconditional uses
  `((tensorPullback g).obj F).IsFiniteLocallyFreeOfRank r` and
  `∃! h : T ⟶ I.subscheme, h ≫ I.subschemeι ≫ W.ι = g`.
  This is exactly ordinary module pullback locally isomorphic to O_T^r
  if and only if unique factorization through C → S. The rank predicate
  is the existing declaration recorded on def-amb-finite-locally-free-module,
  whose free-frame characterization uses free (ULift (Fin r)) on an open
  cover. Neither T nor g has a Noetherian, flatness or reducedness condition.
- The three conjuncts `LocallyOfFinitePresentation W.ι`, `QuasiCompact W.ι`
  and `QuasiSeparated W.ι` give the full finite-presentation convention.
  The same three conjuncts for `I.subschemeι ≫ W.ι` give precisely finite
  presentation of C → S, not merely of C → W.
- The last implication, with the fibre bound at every `s : S`, states
  `IsClosedImmersion (I.subschemeι ≫ W.ι)`, which is exactly the concluding
  assertion that C is closed in S if W_r(F) is the whole base.

Dependency declarations read and used:

| Node | Module | Declaration/interface |
| --- | --- | --- |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | AlgebraicGeometry.IsLocallyNoetherian |
| def-weil-pbc-quasi-compact-scheme | Mathlib.Topology.Defs.Filter | CompactSpace |
| pqf-def-coherent | WeilConjectures.AlgebraicGeometry.Coherent | AlgebraicGeometry.RingedSpace.IsCoherent; Mathlib SheafOfModules.IsQuasicoherent and IsFiniteType |
| def-weil-residue-field | Mathlib.AlgebraicGeometry.ResidueField | Scheme.residueField and Scheme.residue |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | IsClosedImmersion; the canonical subscheme inclusion instance |
| def-pc-module-pullback | Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction | Scheme.Modules.tensorPullback, reexported from WeilConjectures.AlgebraicGeometry.TensorPullback |
| def-weil-pbc-scheme-conventions | convention record, no owning module | LocallyOfFinitePresentation ∧ QuasiCompact ∧ QuasiSeparated |
| def-amb-finite-locally-free-module | WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree | SheafOfModules.IsFiniteLocallyFreeOfRank and its free-cover characterization |
| def-pc-module-stalk-functor | WeilConjectures.Algebra.Homology.ModuleStalkFunctor | RingedSpace.moduleStalkFunctor |

The last two nodes already have published Lean declarations and are added to
stmt_deps under the rule permitting landed dependencies. No new DAG nodes are
needed. Mathlib's ModuleCat.extendScalars and IdealSheafData.subscheme/subschemeι
are used directly; no private definition is created. The canonical ideal-sheaf
construction is in Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme.

The stated proof dependencies are imported as plain imports: the coherence
criterion, FittingIdealGenerateLocally, FittingIdealSheaf,
PresentationFittingIdeal, QuasicoherentFiniteTypeAffine, affine tilde
adjunction, TensorPullbackTilde, open immersion monomorphy, Noetherian opens,
finite-type and finite morphisms, finite presentation over locally Noetherian
bases, local finite-presentation composition, and Nakayama
(Mathlib.RingTheory.LocalRing.Module, IsLocalRing.map_mkQ_eq_top and its tensor
version). Closed-subscheme lifts and quasi-separatedness are already in the
public statement imports. No import cycle was introduced.

Source checked: literature/stacks-project/divisors.tex,
lemma-locally-free-rank-r-pullback (05P8), parts (2) and (3) and the finite
presentation assertion; lemma-fitting-ideal-generate-locally (0C3F) and the
adjacent finite-locally-free Fitting criterion. These give the bounded-generator
open and its closed rank stratum. The node's nine-step proof supplies the
Nakayama identification with residue dimension and the Noetherian specialization.

Edge cases checked before writing:

- r = 0: W is the complement of the support of F, F|W = 0, and I = 0 gives
  C = W. Its composite into S can be open without being closed unless all
  fibre dimensions vanish, exactly as the final conditional states.
- F = 0: W = S for all r. At r = 0 the rank stratum is S; at r > 0 it is
  the empty closed subscheme. Rank on the empty test scheme is vacuous,
  and its unique factorization is included.
- Empty base and empty test scheme: no Nonempty binder or positive-rank
  hypothesis excludes them, and all pointwise clauses have the right meaning.
- A locally free sheaf of constant rank d has W empty for r < d and W = S
  for r ≥ d; its rank stratum is all of S for r = d and empty otherwise.
- For A = k[ε]/(ε²), F = tilde(A/(ε)), r = 1, W = Spec A but C = Spec k.
  This checks nonflat closed base change and shows that the existing free locus
  of F itself cannot replace the universal rank stratum.
- Arbitrary non-Noetherian T is allowed. All schemes and stalk modules use the
  same fixed ambient universe u; no independent smaller test universe makes
  the quantified property vacuous.

Searches made with the prescribed msearch tool:

1. leanfinder, "A coherent sheaf has an open locus where fiber dimension is at
   most r and a closed subscheme of that open universally representing locally
   free pullbacks of rank r": eight hits including Module.isOpen_freeLocus,
   rankAtStalk on the free locus, IdealSheafData and subschemeCover. None
   asserts the requested universal arbitrary-pullback rank stratum.
2. loogle, "Module.freeLocus, AlgebraicGeometry.Scheme.IdealSheafData": zero hits.
3. grep, "Fitting|fittingIdeal|rankLocus|flattening", Mathlib/AlgebraicGeometry:
   zero hits.
4. leansearch, "Fitting ideals represent the functor of pullbacks of a coherent
   sheaf which are locally free of a fixed rank": eight hits on pullback,
   extension of scalars and free-module preservation, none matching the theorem.
5. rg on WeilConjectures and Sheaf for the item id, universalRankLocus,
   universal_rank_locus, exists_coherentUniversalRankLocus: no declaration.
   The only item-id reference is the proof plan of GradedTailRankStratum.
6. rg for IsCoherent and IsFiniteLocallyFreeOfRank found the existing canonical
   definitions read above; these are used rather than copied. The new theorem
   name is absent from dag/lean_names_upstream.json and both source roots.

No mathematical fault or STATEMENT-DISPUTED flag remains. Q59's accepted split
is retained verbatim, including maintainer fields. The previous worker's
unchanged-item rejection is avoided by delivering the actual Lean attachment
and module rather than resubmitting the already accepted split.

## Repair of returned delivery

The immutable head 034bbc6b559e was returned for H13: it rebound the landed
`pqf-def-coherent` record from Q25's `IsQuasiCoherentFiniteType` to
`RingedSpace.IsCoherent`. The sandbox copy of that dependency node is now
removed, so this delivery makes no change to Q25's record or its live users.
The item's theorem and its import of
`WeilConjectures.AlgebraicGeometry.Coherent` are retained exactly as reviewed.
The item's `lean.note` explains that `IsCoherent` is Stacks 01BV and is
equivalent to the landed quasi-coherent finite-type predicate under the
existing `[IsLocallyNoetherian S]` hypothesis. The equivalence is the published
`Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType` in the already
imported `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`.
There are no dependency modules in this repaired delivery.

Compared the retained item node to current main: its only deltas are the Lean
attachment and the two accepted landed statement dependencies
`def-amb-finite-locally-free-module` and `def-pc-module-stalk-functor`.
The mathematical statement, proof, and maintainer fields are unchanged.
The maintainer's independent review accepted every mathematical clause and
edge case; this repair changes no Lean signature, proof plan, or construction.

## Validation

The initial required saved-packet dry run passed (515d298b33d), but still
contained the returned dependency rebind. That packet was not pushed.
After the H13 repair, compilation and a fresh dry run are run through the
prescribed scompile.py and deliver2.py wrappers against the live library.
The only postponed theorem is `exists_coherentUniversalRankLocus`; its proof
remains `by sorry`, with explicit universes and auto-implicit binders disabled.

Repaired-packet validation on 2026-10-22: scompile.py passed both sandbox and
library compilation (7.3 s and 5.9 s). The signature matches `lean.statement`
verbatim, all Lean lines meet the 100-column bound, and the module has exactly
one `sorry`. The fresh deliver2.py --no-push passed server preflight and
compilation at 6ff0d9025eb, staging only this report, the item node, and the item
module. The removed `pqf-def-coherent` node is absent from the delivery.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
