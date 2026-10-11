## Worker report

The module `Sheaf.RingTheory.GRingCompletionRegular` states
`AdicCompletion.isRegular_of_isGRing`, with `sorry` as its sole proof.
No definitions, dependency modules, or new nodes are needed. The node is unchanged
outside its `lean` record.

Hypothesis and clause correspondence:

- A commutative ring A: `(A : Type u) [CommRing A]`, with the universe explicitly bound.
- A is a G-ring (in particular Noetherian): `(hA : IsGRing A)`. The first conjunct of
  the recorded definition is `IsNoetherianRing A`; no separate extra assumption is made.
- Any ideal I of A: `(I : Ideal A)`, with no properness or Jacobson-radical assumption.
- Its I-adic completion: Mathlib `AdicCompletion I A`. Reading Basic.lean shows the
  compatible families in `A / (I^n • top)`, where `I^n • top = I^n`.
- The canonical ring map iota: `algebraMap A (AdicCompletion I A)`. Reading the algebra
  instance in Algebra.lean shows the componentwise quotient map; its
  `algebraMap_apply` theorem identifies this with `AdicCompletion.of`.
- Regularity of iota: `RingHom.IsRegular (algebraMap A (AdicCompletion I A))`.
- Flatness: the first conjunct `f.Flat` in the recorded `RingHom.IsRegular` definition.
- Every prime ideal p: `∀ (p : Ideal A) [p.IsPrime]` in that same definition.
- The fibre: `p.Fiber (AdicCompletion I A)`, Mathlib's canonical residue-field tensor
  product. The dependency definition uses this object as required by the project rule.
- Noetherian and geometrically regular over kappa(p):
  `Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber (AdicCompletion I A))`.
  Its first conjunct is Noetherianity; its remaining clause requires regularity after
  every finite purely inseparable residue-field extension, exactly as the dependency
  node specifies. No clause has been added or removed.

Dependency declarations read and used:

- `Sheaf.RingTheory.GRing`: `IsGRing`, `RingHom.IsRegular`, and
  `Algebra.IsGeometricallyRegular` (full signatures, bodies, and docstrings read).
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, read with its full
  compatible-sequence definition and docstring. Ring and algebra instances come from
  `Mathlib.RingTheory.AdicCompletion.Algebra`, already imported by GRing.

Source verification: the local Stacks TeX is absent on this machine, so read
https://stacks.math.columbia.edu/tag/0AH2 (Lemma 15.51.14), including its proof.
It states exactly the node's theorem for every ideal of a G-ring. The theorem docstring
carries all nine node proof steps, naming the relevant proof dependencies.

Edge cases checked before writing:

- I = top: the completion is the zero ring. A map to the zero ring is flat and its
  fibre rings are zero; regularity allows the zero ring (no prime localizations).
  No proper-ideal or nontrivial-completion hypothesis is imposed.
- I = bot: the completion is canonically A, so the map is an isomorphism and regular.
- A the zero ring: permitted by `[CommRing A]` and `IsGRing A`; its prime quantifier
  is empty, with no spurious domain or nontriviality assumption.
- No local-ring or characteristic restriction occurs. The arbitrary universe u is
  explicit; the existing geometric-regularity definition uses `Type (max u v)` for
  test fields, retaining extensions of the appropriate size.

Searches made (actual msearch records are in searches.jsonl):

- msearch leansearch, query "The completion of a G-ring along an ideal is a regular
  ring homomorphism": service unavailable (Internal Server Error); no verdict taken.
- msearch leanfinder, same query: eight hits, including AdicCompletion.instCommRing,
  instAlgebra, IsAdicComplete.liftRingHom, and IsAdicComplete.henselianRing. None states
  regularity of the completion map.
- msearch loogle, query `AdicCompletion, RingHom.IsRegular`: zero hits, unknown
  identifier RingHom.IsRegular (this predicate is project-specific).
- msearch grep, query `IsGRing|geometrically regular|completion.*regular|regular.*completion`
  in Mathlib/RingTheory: zero hits.
- rg on the full source WeilConjectures tree for `IsGRing|G-ring|geometrically regular|
  completion.*regular|regular.*completion`: zero hits. grep for this exact node id:
  zero hits. rg on the source names index for the node and IsGRing: zero hits.
- rg on lean/Sheaf/RingTheory found the dependency GRing and related results about
  complete local rings, DVR completions, and regular local completions. These have
  different hypotheses or conclusions; none states this arbitrary-ideal theorem.
- rg for `isRegular_of_isGRing` in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no existing declaration with this name.

No statement correction, dispute, or dependency fault was found. Server compilation
and the required delivery dry run are performed before the READY response.

## Second reading by J1

I independently read the delivered node, its nine proof steps, the Lean module,
both statement-dependency nodes, and the definitions in Sheaf.RingTheory.GRing.
The local literature/stacks-project directory is absent. I read the original TeX
from https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
saved only in this item's scratchpad, at lemma-map-G-ring-to-completion-regular
(Tag 0AH2), definition-G-ring (07GH), definition-regular (07BZ), and the
introductory paragraph of section-regular (07BY). I also read
https://stacks.math.columbia.edu/tag/0381, condition (2).
There is no ambient local-ring, proper-ideal, characteristic, or finite-type
hypothesis in 0AH2. The source and node agree without correction.

Object/hypothesis/conclusion inventory and Lean correspondence (H3):

- Commutative ring A: `(A : Type u) [CommRing A]`. PASS: arbitrary commutative
  rings, not just domains, fields, or local rings; universe u is explicitly declared.
- A is a G-ring, including Noetherianity: `(hA : IsGRing A)`. PASS: the dependency
  body's first conjunct is `IsNoetherianRing A`; the second quantifies over every
  prime p and asserts regularity of the canonical map from Localization.AtPrime p
  to its maximal-ideal-adic completion. This is precisely 07GH. No extra
  Noetherian instance is assumed in the theorem.
- Arbitrary ideal I of A: `(I : Ideal A)`. PASS: no properness, finite generation,
  or containment in a specified maximal ideal is assumed. Finite generation
  follows from the G-ring's Noetherianity, as the node proof says.
- The I-adic completion: `AdicCompletion I A`. PASS: I read Basic.lean:171,
  whose carrier consists of compatible families in A/(I^n • top), n : Nat.
  For the ring as its own module these ideals are I^n. Algebra.lean supplies
  componentwise commutative-ring operations. This is the dependency node's
  inverse-limit completion, not a topology-based or maximal-ideal specialization.
- The canonical map iota: `algebraMap A (AdicCompletion I A)`. PASS: I read the
  Algebra instance in Algebra.lean:102 and algebraMap_apply:117, together with
  Basic.lean:364's AdicCompletion.of. Its nth coordinate sends a to its class
  modulo I^n, exactly the map specified in the node.
- Conclusion, iota regular: `RingHom.IsRegular (algebraMap A (AdicCompletion I A))`.
  PASS: I read the dependency's full body, including `letI := f.toAlgebra`.
  Flatness is its `f.Flat` conjunct, for this very ring homomorphism.
- Every prime ideal p of A: the body's `∀ (p : Ideal A) [p.IsPrime]`. PASS:
  all primes are quantified after the fixed canonical map, not only maximal
  ideals or primes containing I.
- Fibre ring: `p.Fiber (AdicCompletion I A)`. PASS: I read Fiber.lean:66:
  it is p.ResidueField tensor over A with the completion. The tensor commutation
  isomorphism identifies this with the source's opposite factor order, with
  its residue-field algebra structure. This uses the established project notion.
- Noetherian fibre: the first conjunct of
  `Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber (AdicCompletion I A))`.
  PASS: explicitly required, not merely regularity of a few localizations.
- Geometrically regular over kappa(p): the remaining conjunct of that predicate.
  PASS: for every finite purely inseparable field extension k'/kappa(p),
  `IsRegularRing (TensorProduct kappa(p) k' fibre)`; I read RegularLocalRing/Defs.lean:92,
  which includes Noetherianity and regularity of every prime localization.
  This matches the dependency node and 0381(2), as recalled in 07BY.

Edge cases: I = top has zero completion, and each fibre and its field base change
is zero; regularity permits this because the zero ring is Noetherian and has
no primes. Maps into zero are flat. I = bot gives A itself (the n = 0 quotient
is zero and compatibility leaves the later coordinates unrestricted beyond
being constant). A = zero is allowed and the prime quantifiers are empty.
No empty-index-set or scheme parameter exists in this theorem. Characteristic
zero and positive characteristic are both covered; the trivial purely
inseparable extension is included even in characteristic zero. The sole carrier
universe is u, and the completion remains in it. The dependency quantifies test
fields in Type (max u v), large enough to contain copies of all finite field
extensions; no undersized test universe makes the condition vacuous.

Independent H4 searches, with different terms from the worker:

- msearch leanfinder: "Formal fibres of the adic completion of a Noetherian G ring
  are geometrically regular"; eight hits. AdicCompletion.flat_of_isNoetherian
  supplies only flatness; smooth-locus, Henselian, completion ring-instance,
  and Hausdorff results do not assert this theorem.
- msearch loogle: `AdicCompletion, IsRegularRing`; no hits.
- msearch grep: `formal.?fibre|formal.?fiber|IsGeometricallyRegular|IsGRing`;
  no Mathlib hits.
- msearch leansearch: "Geometric regularity of all fibres of an ideal-adic
  completion homomorphism for a G ring"; service returned Internal Server Error.
  Recorded as unavailable, not as evidence of absence.
- Independent rg on Mathlib/RingTheory, the full source WeilConjectures tree,
  repository lean/Sheaf, and dag/lean_names_upstream.json for IsGRing,
  IsGeometricallyRegular, isRegular_of_isGRing, and both completion/regular orders.
  No source or Mathlib duplicate. Project GRing is the required definition;
  PolynomialFormalFiber is a special polynomial formal fibre, CompleteLocalGRing
  proves the G-ring condition for complete local rings, FiniteTypeGRing is
  preservation under finite type, CompletionRegularLocal concerns regularity
  of local rings themselves, and DVRCompletionRegular requires a DVR with
  characteristic-zero fraction field. None is this arbitrary-ideal theorem.

H5/H6/H8/H9: no definitions or anonymous proof obligations are delivered; the
single named theorem has only `sorry`. The module and declaration docstrings
name 0AH2 and the exact blueprint id. The nine numbered docstring steps match
the node's nine steps in order: completion flat/Noetherian; maximal localization
reduction; radical containment; quotient/residue identification; flat local map;
completion comparison; transfer of regularity; faithful flatness; descent.
The stated dependency names are retained in each step. The single import GRing
supplies the predicates and completion instances used in the signature.
Namespace AdicCompletion has no Sheaf prefix, no name collision was found,
all lines are at most 100 characters, and every variable/universe is bound.
I checked lean.statement byte-for-byte against the signature before `:= by`.

H12/H13 and correction checks: there are no new nodes, dependency modules,
private definitions, missing notions, or statement_change record to audit.
Both recorded dependencies are usable exactly as delivered. No mismatches
were found. I left the Lean module and node unchanged and appended this
independent reading to the worker report. Server compilation, the dry-run
preflight, and delivery are run after this reading.
