## Worker report

The module `Sheaf.RingTheory.WContractibleGeometricCriterion` states
`RingHom.exists_retraction_of_wlocal_geometric_criterion`, with its proof postponed.
It introduces no definitions and changes only the item's `lean` record.
Source read: Stacks Project proetale.tex, Tag 0982, implication (3) to (1).
The source explicitly equates splitting faithfully flat ind-etale maps with splitting
faithfully flat weakly etale maps via its refinement proposition.

Clause-by-clause correspondence:

- A commutative ring R: `{R : Type u} [CommRing R]`.
- Spec R is w-local: `[IsWLocalRing R]`. Its `WLocalSpace` supplies closedness of
  closed points and the unique closed point in each connected component, as explained
  in the recorded dependency and its connected-components equivalence.
- The quotient space of connected components is extremally disconnected:
  `[ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))]`.
  Mathlib's class says precisely that the closure of every open subset is open.
- Every maximal localization is strictly henselian: `hstrict : ∀ (m : Ideal R)
  [m.IsMaximal], IsStrictlyHenselianLocalRing (Localization.AtPrime m)`.
  Maximality supplies the prime instance needed by `Localization.AtPrime`.
- Every commutative ring B and ring map f: `{B : Type v} [CommRing B]
  (f : R →+* B)`. The universes u and v are independent.
- Faithfully flat: `(hfaithful : f.FaithfullyFlat)`, using the algebra structure
  induced by f, not an unrelated structure on B.
- Weakly etale: `(hweak : f.WeaklyEtale)`, again using f.toAlgebra. This is the
  recorded `Algebra.WeaklyEtale`, flat over R and flat under tensor multiplication.
- Existence of a ring-map retraction and its identity: `∃ r : B →+* R,
  r.comp f = RingHom.id R`.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.ProEtale.WLocal`: `IsWLocalRing`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`,
  extending `HenselianLocalRing` with separably closed residue field.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`, which
  specializes `Module.FaithfullyFlat` to f.toAlgebra.
- `Sheaf.RingTheory.IndPrincipalZariski`, through its public imports:
  `Algebra.WeaklyEtale` and `RingHom.WeaklyEtale` (the upstream ring-map wrapper).
- Mathlib `ConnectedComponents`, `PrimeSpectrum`, `Localization.AtPrime`, and
  `ExtremallyDisconnected` render the other standard objects.

The declared proof-dependency modules are imported: retained localization,
ind-etale stability, prime localization, faithful-flat spectrum results, and
`WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale` (strict local theorem).
Unstated proof dependencies need no imports and are not prerequisites to typing
this statement. The five-step proof docstring follows the node's complete plan.

Edge cases: no nonzero-ring, inhabited-spectrum, or existence-of-maximal-ideal
hypothesis is imposed. For the zero ring R any unital map forces B to be zero;
maximal-ideal hypotheses are then vacuous and the retraction conclusion holds.
For a separably closed field, the criterion specializes to the strict local case.
Disconnected spectra are allowed; extremal disconnectedness is required of the
component quotient, not of the whole spectrum. Arbitrarily large B are allowed
by the independent universe v. The identity map is included. No node fault or
statement correction was found.

Searches (2026-10-15):

- msearch leanfinder, query “A w-local ring with extremally disconnected space of
  connected components and strictly henselian localizations at maximal ideals admits
  a retraction of every faithfully flat weakly etale ring map”: eight hits on etale
  algebra, RingHom.Etale, and etale loci; no matching criterion.
- msearch loogle, query `RingHom.WeaklyEtale, RingHom.FaithfullyFlat`: zero hits,
  unknown identifier RingHom.WeaklyEtale in the Mathlib service.
- msearch grep, query `WContractible|w.contractible|ExtremallyDisconnected` in
  Mathlib RingTheory: zero hits.
- msearch leansearch, query “w-local ring extremally disconnected connected
  components strictly henselian local rings weakly etale faithfully flat retraction”:
  service unavailable (Internal Server Error).
- rg in upstream WeilConjectures and the read-only group framework for
  `Extremally|extremally|retract|retraction|split|StrictlyLocal`: found and read
  `IsWContractibleRing.exists_retraction` in ProEtale/WContractible.lean.
  It only quantifies over ind-etale algebras in the base universe, so does not state
  this node's weakly etale criterion. Its auxiliary retractions also require a
  special closed-point presentation or stalk isomorphisms, not this statement.
- rg for `wcontractible-geometric|geometric.*criterion|exists_retraction.*weak|
  retraction_of.*[Gg]eom` in upstream WeilConjectures and lean/Sheaf found no
  matching declaration. A search for the literal node id in upstream sources
  likewise found none. The chosen full declaration name has no existing match.

Validation: scompile.py compiled the delivered module cleanly in 1.5 seconds
(nice 19, two threads, 60 seconds per file). The deliver2.py --no-push dry run
printed OK: compilation and preflight passed, with only the independent second
reading left for the second reader. Nothing was pushed. No local Lean compiler
or global build was run.

## Second reading by NQ

I independently read the node JSON, the complete delivered module, and Stacks
proetale.tex, lemma-w-local-strictly-henselian-extremally-disconnected (Tag 0982),
including the preceding definition and the entire proof. The section assumes only
commutative rings; it imposes no nonzero, finiteness, characteristic, or Noetherian
condition. Clause (3) is precisely the three hypotheses below. The preceding
remark and the first sentence of the proof identify splitting ind-etale covers
with splitting weakly etale covers. Thus the node and Lean correctly state the
full implication (3) to (1), not merely its ind-etale intermediate step.

Object/hypothesis/conclusion inventory and matching (all pass):

1. A commutative ring R: `{R : Type u} [CommRing R]`. No extra algebra structure
   or field hypothesis is introduced.
2. The Zariski spectrum of R is w-local: `[IsWLocalRing R]`. I opened the
   recorded WLocal module and its WLocal/Basic and WLocal/ConnectedComponents
   dependencies. `IsWLocalRing` supplies `WLocalSpace (PrimeSpectrum R)`.
   That class says closed points form a closed subset and closed specializations
   are unique; the displayed `isHomeomorph_connectedComponents_closedPoints`
   identifies this with exactly one closed point per connected component.
   Spectrality is automatic for a prime spectrum, so the class adds no condition.
3. The quotient space of connected components, not the whole spectrum, is
   extremally disconnected:
   `[ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))]`.
   I opened Mathlib's class: its only field says open sets have open closure.
   ConnectedComponents carries the actual quotient topology.
4. For every maximal ideal m, the local ring R_m is strictly henselian:
   `hstrict : ∀ (m : Ideal R) [m.IsMaximal],
   IsStrictlyHenselianLocalRing (Localization.AtPrime m)`.
   I opened the recorded Henselian module: this class extends
   `HenselianLocalRing` and requires `IsSepClosed` of the residue field.
   Maximality supplies primality for this exact localization; no condition on
   all prime localizations or on R itself being local is assumed.
5. Every commutative ring B and every map f from R to B:
   `{B : Type v} [CommRing B] (f : R →+* B)`. The arbitrary universe v is
   independent of u. Implicit binders still universally quantify B.
6. The map f is faithfully flat: `hfaithful : f.FaithfullyFlat`. I opened
   Mathlib/RingTheory/RingHom/FaithfullyFlat: the definition is precisely
   `Module.FaithfullyFlat R B` for `f.toAlgebra`, the ring-map notion recorded
   by def-weil-pbc-faithfully-flat-ring-map.
7. The same map is weakly etale: `hweak : f.WeaklyEtale`. I read
   def-weil-pbc-ind-etale-algebra and its IndPrincipalZariski module/public
   imports, then opened the upstream RingHom.WeaklyEtale wrapper and Mathlib's
   Algebra.WeaklyEtale class. The wrapper uses f.toAlgebra; the class requires
   flatness over R and flatness of tensor multiplication. It is exactly the
   dependency's weakly etale clause, not its principal ind-Zariski predicate.
8. There exists a ring map in the reverse direction:
   `∃ r : B →+* R`. The existential follows all hypotheses and the choice of f.
9. Its composite with this f is the identity:
   `r.comp f = RingHom.id R`. This is equality of unital ring maps and has
   the specified orientation; no isomorphism or extra uniqueness is claimed.

Edge cases: the zero ring and empty spectrum are included, with the maximal
ideal condition vacuous. A unital map from the zero ring forces B to be zero,
so the conclusion is appropriate. No inhabited index or spectrum is assumed.
Disconnected spectra and all characteristics are allowed; a separably closed
field and the identity map are included. There is no integer degree or index
set in this statement. Independent universes u and v exclude no relative size
of R and B. No unbound variables or universes occur.

Independent searches, using different wording from the first reader:

- msearch leanfinder: "A commutative ring whose component space is Stonean and
  whose maximal localizations are strictly henselian splits faithfully flat
  weakly etale homomorphisms": eight hits about Etale/IsEtaleAt and local
  etaleness, no splitting criterion.
- msearch loogle: `"retraction", "FaithfullyFlat"`: zero hits.
- Direct rg on Mathlib RingTheory, upstream WeilConjectures and project
  lean/Sheaf for `Stonean`, `splits.*[Ww]eakly`,
  `retraction.*[Ww]eakly`, `geometric_criterion` and the literal node id:
  no matching declaration. The Stonean hit was the WContractible import.
- I separately opened upstream WContractible.lean at
  `exists_retraction_of_bijectiveOnStalks`,
  `IsWContractibleRing.exists_retraction_of_zeroLocus_map_eq_closedPoints`,
  and `IsWContractibleRing.exists_retraction`. The first two require stalk
  identification/closed-point presentation data. The last assumes ind-etaleness
  and both rings in Type u. None is the present statement, so dropping the
  module and marking an exact existing match would be incorrect.

H4/H5/H6/H8/H9: no definitions or new/dependency nodes are delivered, hence no
hollow construction, private copy, or new-node audit is needed. The sole theorem
has exactly a sorry proof. Its source/blueprint docstring reproduces all five
node proof steps: refinement, retained localization, strict local isomorphisms,
faithful flatness, and the final retraction. Recorded proof-dependency modules
are imported where present; genuinely unstated proof dependencies do not prevent
stating this theorem. Namespace, public imports, and line lengths are appropriate.
There is no statement_change, so no correction/citer audit is required.

Mismatches found: none. Changes: appended this independent reading only; retained
the correct Lean module and the verbatim lean.statement signature unchanged.
