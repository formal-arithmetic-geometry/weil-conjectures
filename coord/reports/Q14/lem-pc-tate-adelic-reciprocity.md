## Worker report

The module `Sheaf.RingTheory.TateResidue.AdelicReciprocity` states
`TateResidue.adelic_reciprocity`, with its entire proof postponed by `sorry`.
There are no definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` record changes. The docstring gives all eight proof steps.

Hypothesis and conclusion correspondence:

- Fields k contained in K: `(k : Type u) (K : Type v) [Field k] [Field K]
  [Algebra k K]`. A field algebra map is injective, so this is a field inclusion.
- Any set I: `(I : Type w)`, with an independent explicit universe and no
  nonemptiness, finiteness, or decidable-equality restriction.
- Subrings containing k: `(O : I → Subalgebra k K)`, using the same subalgebra
  encoding as the recorded DVR-residue dependency.
- Every O_i is a DVR: `[∀ i : I, IsDiscreteValuationRing (O i)]`.
- Every O_i has fraction field K: `[∀ i : I, IsFractionRing (O i) K]`, using
  the canonical algebra structure from the subalgebra inclusion.
- Finite residue extension: `[∀ i : I, FiniteDimensional k
  (IsLocalRing.ResidueField (O i))]`. No separability or perfectness is assumed.
- Finitely many nonintegral coordinates for every f: `hfin : ∀ f : K,
  {i : I | f ∉ O i}.Finite`.
- The specified map P is `TateResidue.principalParts O hfin`. Its source is K,
  its target is `Π₀ i : I, K ⧸ (O i).toSubmodule`, the dependent finitely supported
  family/direct sum, and `principalParts_apply` says its i-th value is the class of f.
  It is an existing construction, not an arbitrary map supplied as a hypothesis.
- Finite-dimensional intersection: `hH0 : FiniteDimensional k
  (⨅ i : I, O i : Subalgebra k K)`; the carrier is precisely the intersection.
- Finite-dimensional cokernel of P: `hH1 : FiniteDimensional k
  ((Π₀ i : I, K ⧸ (O i).toSubmodule) ⧸ LinearMap.range (principalParts O hfin))`.
  For vector spaces, this quotient by the image is the cokernel.
- Every differential: `(ξ : KaehlerDifferential k K)`.
- The local residues are `localRes (O i) ξ`. The imported
  `TateResidue.dvr_residue_calculus` identifies exactly this existing map with
  the finite-potent projection-commutator trace in the dependency node.
- Only finitely many residues are nonzero: `(Function.support fun i : I ↦
  localRes (O i) ξ).Finite`.
- Their sum vanishes: `∑ᶠ i : I, localRes (O i) ξ = 0`, conjoined with the
  finite-support assertion so this is the actual finite sum of local residues.

Dependency interfaces read and used:

- `Sheaf.RingTheory.TateResidue.DVRResidueCalculus`, full signature/docstring of
  `TateResidue.dvr_residue_calculus`, and its imported existing
  `WeilConjectures.RingTheory.TateResidue.LocalResidue`, `TateResidue.localRes`.
  The public import keeps the recorded dependency interface available.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  and `KaehlerDifferential.linearMapEquivDerivation` (full definitions/docstrings
  read). They give the same differential module, derivation, and universal property.
  This module is transitively publicly imported by the residue interface.
- `WeilConjectures.RingTheory.TateResidue.ResidueTheorem`:
  `TateResidue.principalParts`, `principalParts_apply`, and `residue_theorem`.
  The latter is a general theorem with an explicit admissibility hypothesis and
  arbitrary commutative algebra K. It does not have the node's exact signature:
  the present DVR statement must obtain admissibility from the DVR calculus
  rather than ask for it. It is not recorded as an exact existing match.
- The two abstract proof-dependency nodes have no recorded Lean module locally.
  No new interface is needed to state this item. Their existing mathematical
  counterparts (`res`, the vanishing properties, `res_sup_add_res_inf`) are already
  imported through the upstream residue theorem. Their node ids appear at their
  respective steps in the proof docstring; no duplicate is introduced.

Sources checked: Tate's original PDF, printed pp. 153–157, especially R5,
Theorem 3, its corollary, and the finite-set decomposition in its proof.
The uncompleted K factors are the node's specified adaptation; the argument only
uses finite principal parts and the two finite-dimensional hypotheses.

Edge cases checked before writing:

- Empty I is allowed. The residue family and sum are empty. The intersection is
  the top subalgebra K, and the theorem retains exactly its stated finiteness
  hypothesis even in this case. No diagonal injectivity is used in the empty case.
- Zero differential gives zero local residues and empty support by linearity.
- Empty support bounds S, and empty complement I minus S, are both allowed in
  the finite-decomposition proof. No singleton or nonempty index hypothesis occurs.
- Finite families and repeated DVRs are not excluded. All given finiteness
  hypotheses remain present; none has been silently replaced by curve geometry.
- Positive characteristic, imperfect k, and inseparable residue extensions are
  included: there is no coefficient-field or classical-residue assumption.
- All three universes and every variable are explicitly bound; `autoImplicit` is false.

Searches made using the required `msearch.py Q14 lem-pc-tate-adelic-reciprocity` wrapper:

- `leanfinder`, query: "Sum of local Tate residues of a differential is zero for
  discrete valuation subrings with finite dimensional principal parts cokernel".
  Eight hits, on DVR cotangent dimensions, Dedekind zeta residues, and elliptic
  valuation facts; none is the algebraic residue theorem. Returned signatures read.
- `loogle`, query: "TateResidue.residue_theorem, finsum". Zero hits; the service
  does not know the project-local `TateResidue.residue_theorem` identifier.
- `grep`, query: "residue_theorem|localRes|principalParts". Zero Mathlib hits.
- `leansearch`, query: "The sum of the local residues of a differential is zero
  for a family of discrete valuation subrings with finite dimensional principal
  parts cokernel". Eight hits on DVR equivalences, cotangent dimension, and
  residue-field constructions; no reciprocity theorem. Returned signatures read.
- Direct `rg` in `lean/WeilConjectures` for reciprocity, residue_theorem,
  principalParts, and Adelic found the existing abstract theorem and canonical
  principal-parts construction, whose full source was read. Direct item-id search
  found no declaration attached to this node.
- Direct `rg` in `lean/Sheaf` for tate-adelic, residue_theorem, and
  adelic_reciprocity found no duplicate. The already recorded DVR calculus module
  was read and reused.

Validation: `scompile.py Q14 lem-pc-tate-adelic-reciprocity
.../AdelicReciprocity.lean` compiled both its sandbox check and library-module
check cleanly (7.8 s and 6.2 s); no errors or warnings were printed.
No statement fault or dispute was found.

## Second reading by Q14

The dispatcher explicitly forbids starting other agents. This is an author
rereading; the maintainer's independent review remains the independent reading.
I reopened the JSON statement and the final Lean file and compared every clause.
The field inclusion uses the injective field algebra map, the DVRs are the same
subalgebras used by `dvr_residue_calculus`, and all three local instance families
(DVR, fraction field, finite residue field) are present. `hfin` quantifies over
every f. I checked the actual existing `principalParts` body and its coordinate
formula, so the quotient in `hH1` is the specified cokernel. `hH0` is the literal
intersection, including the empty-index convention. The conclusion has both
finite support and vanishing sum for every ξ. No admissibility, separability,
nonemptiness, or geometric hypothesis was added. The earlier upstream theorem
was rejected as an exact existing match because of its additional admissibility
binder; its canonical map was reused. No mismatches or changes were found in
this rereading. The recorded signature is extracted verbatim from the file.
