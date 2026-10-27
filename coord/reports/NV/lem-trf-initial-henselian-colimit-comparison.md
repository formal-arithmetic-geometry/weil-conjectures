## Worker report

The module `Sheaf.RingTheory.InitialHenselianColimitComparison` states
`Algebra.initial_henselian_colimit_comparison`, with one `sorry` and no new
definitions. The node is already split and reviewed at stage 1, but has no Lean
record on the read base. This delivery adds that record only; it does not split
the node again. There is no repair note for this item in the read clone.

The complete hypothesis and conclusion correspondence is as follows.

- The commutative local base is `R : Type u`, `[CommRing R]`, `[IsLocalRing R]`.
  Its residue field `k = R/m` is Mathlib's `IsLocalRing.ResidueField R`.
- The commutative henselian local rings `C,H` have `[CommRing C]`,
  `[HenselianLocalRing C]`, and the corresponding instances for `H`.
- The specified structural maps are `algebraMap R C` and `algebraMap R H`,
  supplied by `[Algebra R C]`, `[Algebra R H]`. Their locality is the two
  `IsLocalHom` instances. For local rings this says exactly that the inverse
  image of the maximal ideal is the maximal ideal: these ideals are the
  nonunits; homomorphisms preserve units, and `IsLocalHom` reflects units.
- `hC` uses the recorded `RingHom.IndEtaleAcrossUniverses` predicate on the
  specified structural map. This is the published canonical ULift transport
  of the existing ind-etale predicate, not a new presentation assumption.
- `hres` asserts bijectivity of the induced structural residue field map
  `IsLocalRing.ResidueField.map (algebraMap R C)`. Bijectivity of this ring map
  is exactly being a residue field isomorphism, without a chosen identification.
- `hH` quantifies over henselian local commutative `T` and every local ring
  map `a : R →+* T`. Its `∃! b` is uniqueness among all local ring maps
  `H →+* T` with `b.comp (algebraMap R H) = a`. No residue field condition or
  ind-etale condition is imposed on `H`.
- `∃ (f : C →ₐ[R] H) (g : H →ₐ[R] C)` supplies the specified `R`-algebra
  maps. The next two clauses assert their locality. The two universally
  quantified clauses assert uniqueness of each map among all local
  `R`-algebra maps in the respective direction.
- `g.comp f = AlgHom.id R C` and `f.comp g = AlgHom.id R H` give the two
  inverse identities. Together with the `AlgHom` structures these say that
  `f` is an isomorphism over the specified maps from `R`.
- The final universal quantifier covers arbitrary commutative `P` and
  `P → R`, encoded by `[CommRing P]` and `[Algebra P R]`. The structures
  `[Algebra P C]`, `[Algebra P H]` and scalar towers specify exactly the
  composites through `R`; they do not impose extra conditions on `P → R`.
- `I : Type u`, `[SmallCategory I]`, `[IsFiltered I]`, and
  `D : I ⥤ CommAlgCat.{u} P` encode a small filtered diagram of commutative
  `P`-algebras. All objects use an arbitrary common universe `u`; in particular
  the test-ring universe is not below the base-ring universe, and the index
  universe agrees with the rings as required by the project convention.
- `legs : D ⟶ (Functor.const I).obj (CommAlgCat.of P C)` is exactly the
  specified compatible family `lambda_i : D_i → C`. Algebra linearity of
  these legs says that their induced `P → C` is the specified composite.
- The `IsColimit` antecedent on the image of this cocone under `forget₂`
  assumes the full ring-colimit universal property, not just a colimit of
  underlying sets or an abstract isomorphism of colimit objects.
- Both conclusion cocones are literally
  `(Cocone.mk (CommAlgCat.of P C) legs).extend
  (CommAlgCat.ofHom (f.restrictScalars P))`.
  Their vertex is the specified `H` with composite `P`-algebra structure, and
  their legs are `f lambda_i`. The first `Nonempty (IsColimit ...)` asserts
  the ring-colimit property after `forget₂`; the second asserts the
  commutative `P`-algebra-colimit property for those same maps. `Nonempty`
  only turns universal-property proof data into a proposition; it chooses
  neither maps nor objects.
- The final implication assumes `Algebra.Etale P (D.obj i)` and
  `Algebra.FinitePresentation P (D.obj i)` at every stage, and concludes
  `RingHom.IndEtaleAcrossUniverses (algebraMap P H)` for the specified map.
  In conjunction with the preceding two cocone clauses this is the claimed
  transferred ind-etale presentation, with no existential replacement of legs.

Dependencies read and reused:

- `Sheaf.RingTheory.IndEtaleUniverseTransport`:
  `RingHom.IndEtaleAcrossUniverses`, with the public upstream
  `Algebra.IndEtale` from
  `WeilConjectures.RingTheory.ProEtale.IndEtale`. The latter's definition is
  a filtered `ColimitPresentation` with etale stages.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded terminology
  module. The relevant class is Mathlib's `HenselianLocalRing`; the
  upstream `IsStrictlyHenselianLocalRing` specialization is not assumed.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, and
  `Cocone.extend`; `CategoryTheory.IsFiltered` from the public filtered API.
  The signatures and universal property were read in `Cones.lean`,
  `IsLimit.lean`, `HasLimits.lean`, and `Filtered/Basic.lean`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`,
  publicly available through the ind-etale dependency.
- `Mathlib.RingTheory.Etale.Basic`: `Algebra.Etale`, the ring-algebra
  formulation permitted by STATE's ETALE RING MAPS convention. The
  recorded scheme definition in `Mathlib.AlgebraicGeometry.Morphisms.Etale`
  and its affine-ring interpretation were also read.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`:
  `IsLocalRing.ResidueField.map`, the canonical map induced by a local map.
- Proof-only import `WeilConjectures.RingTheory.MapIntoHenselianColimit`:
  `Algebra.map_into_henselian_colimit`, whose full signature and proof
  docstring were read. It is the only additional proof dependency with a
  separate module; other proof dependencies are already statement imports.

Source check: read `literature/stacks-project/algebra.tex`,
`lemma-map-into-henselian-colimit` (Tag 08HR), and the following uniqueness
lemma, which assumes both algebras ind-etale and therefore is not a match.
Read `categories.tex`, `definition-colimit` (Tag 002F), for the entire cocone
universal property, and `proetale.tex`, `definition-ind-etale` (Tag 097I).
The theorem docstring carries all five node proof steps, including the
prescribed-residue uniqueness argument and the nonempty-index argument for
algebra linearity of the ring mediator.

Edge cases checked before writing: a field base; `C = R` already henselian;
`C = H`; the singleton filtered diagram; transition maps without injectivity;
and a noninjective map `P → R`. There is no domain, reducedness, injectivity,
Noetherian, or characteristic assumption. A zero base cannot be local in the
usual nontrivial local-ring sense. The zero `P` case has no map to nonzero
`R`, as in the informal statement. Empty diagrams are excluded exactly by
`IsFiltered`, which includes nonemptiness. The initial property is among all
local maps, not just those inducing one chosen residue identification.

Searches (2026-10-22):

- `msearch.py ... leanfinder`: "An ind etale henselian local algebra with
  unchanged residue field is uniquely isomorphic to an initial henselian
  local algebra and transfers colimit cocones". Eight results: henselian
  classes/TFAE and standard-etale lifting and homomorphism results; none
  states the initial comparison or cocone transfer.
- `msearch.py ... leansearch`: "Initial henselian local algebra is uniquely
  isomorphic to an ind etale henselian local algebra inducing an isomorphism
  on residue fields". Eight results, including the henselian terminology,
  root-lifting TFAE, canonical residue map, and formal-etale definition;
  no complete match.
- `msearch.py ... loogle 'HenselianLocalRing'`: seven results, consisting of
  the class, field instance, maximal-ideal henselian instance, and root
  lifting/TFAE; no match.
- `msearch.py ... grep
  'henselization|henselisation|henselian.*[Ee]quiv|[Ee]quiv.*henselian'
  RingTheory`: two Mathlib hits in Henselian.lean, both documentation;
  no matching declaration.
- `rg -n` for the same henselization terminology and initial-henselian
  comparison in the named `lean/WeilConjectures` and `lean/Sheaf` trees:
  existing strict henselization constructions and related results, no
  initial comparison for ordinary henselian local algebras. Exact searches
  for the node id and proposed declaration name in these two trees and
  `dag/lean_names_upstream.json` found no declaration. No notion is duplicated.

Validation: the module compiles cleanly through the prescribed `scompile.py`
in both sandbox and library-module modes (1.6 seconds each). No `#check`
commands or local notation remain. All universes and variables are explicit;
`autoImplicit` is disabled. No statement correction or new node is needed.

## Second reading by NV

This is the dispatched worker's own second reading; the maintainer supplies
the independent review. Reopened the node and Lean file and matched every
hypothesis and clause as above. In particular, `hH` has no residue-field or
presentation premise; `hres` is on the structural residue map rather than
an unrelated field equivalence; the uniqueness clauses range over all local
algebra maps; and both inverse identities are present. The colimit premise
is in rings and the two conclusions use the same extended cocone in rings
and algebras, with the specified composite `P`-structure. The conditional
ind-etale conclusion retains the etale and finite-presentation conditions
on every stage. No clause is left implicit in an abstract object isomorphism.
The original Greek lambda binder was a reserved token and was renamed
`legs` during compilation; no mathematical statement changed. The final
signature has no other mismatch with the node. No dispute remains.
