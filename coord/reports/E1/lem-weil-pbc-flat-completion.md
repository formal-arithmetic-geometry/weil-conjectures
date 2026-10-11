## Worker report

The module states `flat_adicCompletion_of_flat_local` in
`lean/Sheaf/RingTheory/FlatCompletion.lean`. It uses the Mathlib notions
`IsNoetherianRing`, `RingHom.Flat`, and `AdicCompletion` recorded by the three
statement dependencies. The theorem has explicit commutative-ring, local-ring,
and Noetherian instances for `A` and `B`, a ring homomorphism `φ`, its flatness,
and the local condition that maximal-ideal elements map into the maximal ideal.
It introduces `mA`, `mB`, the two adic completions and canonical algebra maps,
and asserts existence of the completion map `φhat`. The levelwise clause uses
`AdicCompletion.evalₐ` and the quotient lift induced by `φ`; the compatibility
clause is `φhat.comp ιA = ιB.comp φ`; the conclusion is `φhat.Flat`.

The levelwise quotient map is well-defined because the local condition implies
`mA.map φ ≤ mB`, hence `(mA ^ n).map φ ≤ mB ^ n`; this is rendered explicitly
in the theorem signature. The existential formulation packages the map whose
coordinate maps are exactly the displayed maps, together with the canonical-map
identity and flatness. All theorem proof content is `sorry`, as required for
stage 2.

Dependencies used: `def-weil-pbc-noetherian-ring` → Mathlib `IsNoetherianRing`;
`def-weil-pbc-flat-ring-map` → Mathlib `RingHom.Flat`; and
`def-weil-pbc-adic-completion` → Mathlib `AdicCompletion`.

Edge cases checked: `n = 0` is admitted by the quotient-level formulation;
zero ideals and the zero maximal-ideal case are not excluded; universes of `A`
and `B` are independent (`u`, `v`). The local condition is stated for every
member of the maximal ideal, including zero.

Searches made: `msearch.py leanfinder` and `msearch.py loogle` for flat maps of
adic completions (no exact map theorem; only `AdicCompletion.flat_of_isNoetherian`)
and `msearch.py grep` over `Mathlib/RingTheory/AdicCompletion` (only the
one-ring completion-flat theorem); `rg` over the project source found no
existing declaration for this node. The recorded dependency declarations were
checked in their Mathlib source files and match the node notions exactly.


## Second reading by E1

I independently read the sandbox node and module, all three dependency node
records and their actual Mathlib declarations, and Stacks more-algebra.tex,
lemma-flat-completion (Tag 0C4G), lines 10731–10763. The repository has no
local Stacks checkout; the source text was read in the existing local copy
/home/ubuntu/c1-stacks-review/more-algebra.tex. The lemma assumes precisely
Noetherian local commutative rings and a local homomorphism. The node selects
the forward implication of the source equivalence; this is legitimate and
needs no node correction.

Object/hypothesis/conclusion checklist:

- A and B are arbitrary commutative rings: `(A : Type u) (B : Type v)` and
  `[CommRing A] [CommRing B]`. Match, with independent universes.
- Both rings are local: `[IsLocalRing A] [IsLocalRing B]`; their maximal
  ideals are `let mA := IsLocalRing.maximalIdeal A` and likewise mB. Match.
  I read LocalRing/Defs.lean and MaximalIdeal/Defs.lean: local rings are
  nontrivial, as in the source's unique-maximal-ideal convention.
- Both rings are Noetherian: `[IsNoetherianRing A] [IsNoetherianRing B]`.
  Noetherian/Defs.lean defines this as `IsNoetherian R R`, and
  `isNoetherianRing_iff_ideal_fg` gives exactly finite generation of ideals.
  This matches def-weil-pbc-noetherian-ring without stronger assumptions.
- The given ring map is `(φ : A →+* B)`; flatness is `(hφ : φ.Flat)`.
  RingHom/Flat.lean defines this as Module.Flat A B using φ.toAlgebra,
  exactly def-weil-pbc-flat-ring-map, with no preselected algebra instance.
- Locality is `hlocal : ∀ x : A, x ∈ IsLocalRing.maximalIdeal A →
  φ x ∈ IsLocalRing.maximalIdeal B`. This is precisely the node's explicit
  maximal-ideal condition, without an extra hypothesis.
- The completions are `AdicCompletion mA A` and `AdicCompletion mB B`.
  Basic.lean defines compatible families in M / (I^n • top); for M = R,
  Algebra.lean's evalₐ identifies these quotients with R / I^n. The ring
  structure and projections are exactly def-weil-pbc-adic-completion.
- The canonical maps are `ιA := algebraMap A Ahat` and likewise ιB.
  Algebra.lean's algebraMap_apply and evalₐ_of show these send a to its
  residues. Match.
- The induced map is existentially packaged as `∃ φhat : Ahat →+* Bhat`.
  Its first conjunct specifies every quotient coordinate via
  `Ideal.Quotient.lift (mA ^ n) ((Ideal.Quotient.mk (mB ^ n)).comp φ)`.
  The included well-definedness proof uses hlocal and Ideal.map_pow,
  not a new assumption. This is the node's coordinatewise map. The
  projections jointly determine a completion element (ext_evalₐ), so the
  existential packaging cannot select a different map.
- Compatibility is exactly `φhat.comp ιA = ιB.comp φ`.
- The conclusion is exactly `φhat.Flat`, for that same coordinatewise map.
  Neither faithful flatness nor the source's reverse implication is added.

Edge cases: n ranges over all naturals, including zero; at n = 0 both
quotients are by the unit ideal and the coordinate condition is valid.
Fields (zero maximal ideals) are included. Zero rings are excluded by the
source's local-ring convention, not by a new constraint. No index set of
rings, scheme, or zero module is quantified here; empty-scheme and empty-index
cases do not apply. There is no characteristic, dimension, finite-type,
residue-field, or common-universe restriction. All variables and universes
are explicitly bound.

Independent searches on 2026-10-11:

- msearch.py leansearch: “A flat local ring map induces a flat map on the
  completions at the maximal ideals”: service unavailable (Internal Server
  Error); no verdict drawn from this unavailable search.
- msearch.py leanfinder: “flatness of the induced homomorphism between
  maximal ideal completions of two local rings”: eight hits, including
  RingHom.Flat.localRingHom (localization, not completion),
  Module.FaithfullyFlat.of_flat_of_isLocalHom (given flatness), and
  AdicCompletion.flat_of_isNoetherian (R to its own completion only).
  None states this node.
- msearch.py loogle: `AdicCompletion, RingHom.Flat`: zero hits.
- rg with completion/flat in both orders and the proposed declaration name
  over Mathlib/RingTheory/AdicCompletion, WeilConjectures and repository
  lean/Sheaf: no exact theorem. I opened FlatModuleCompletion.lean:
  Module.flat_adicCompletion completes at an ideal of the base, rather than
  B's maximal ideal, so is not this statement. I also opened
  FlatLocalCompletionIso.lean: RingHom.flat_local_completion_iso assumes
  equality of extended maximal ideals and bijectivity on residue fields,
  and is not this theorem. No duplicate definition or theorem is introduced.

Mismatch and repairs: the statement docstring lacked all five node proof
steps (H8). I added them with the dependency identifiers, including transport
of quotient module structures and the hypotheses of the powers criterion.
I replaced the unnecessarily broad AdicCompletion.LocalRing import with
LocalRing.MaximalIdeal.Defs, removed unused TensorProduct scope, and added
an ordinary copyright header. The mathematical signature is unchanged;
lean.statement now preserves its exact multiline text. No hollow definition,
new node, dependency module, statement correction, or proved theorem is present.
The only theorem body remains sorry. The term proof inside the quotient lift
is well-definedness of existing Mathlib data, with no postponed proof.
