## Worker report

The module `lean/Sheaf/AlgebraicGeometry/TameUnitExtensionCharacter.lean` states
`AlgebraicGeometry.exists_tame_unit_extension_character`.  It has no proof beyond the
required `sorry`.  The canonical group completion is
`Algebra.GrothendieckGroup M`; the unit identification is the multiplicative
isomorphism `unitEquiv : Aˣ ≃* Mˣ`, and the induced unit map is recorded by `i` and
`hi`.

The first hypotheses render the strictly henselian local ring and finite group action:
`A : Type u`, `[CommRing A]`, `[IsStrictlyHenselianLocalRing A]`,
`H : Type u`, `[Group H]`, `[Finite H]`, and
`ρ : H →* (A ≃+* A)`.  The clause that the action induces the identity on the residue
field is `hres`, namely
`∀ h a, IsLocalRing.residue A ((ρ h) a) = IsLocalRing.residue A a`.

The commutative monoid and its identified units are rendered by
`M : Type u`, `[CommMonoid M]`, and `unitEquiv : Aˣ ≃* Mˣ`.  The finitely generated
free abelian group is rendered by `L : Type u`, `[AddCommGroup L]`,
`[Module.Free ℤ L]`, and `[Module.Finite ℤ L]`.  The positive monoid is the explicit
submonoid `Lplus : Submonoid (Multiplicative L)`.  Its fine saturated, sharp, and
generating clauses are respectively `hLfs`, `hLsharp`, and
`hLgen : Subgroup.closure (Set.range Lplus.subtype) = ⊤`.

The tameness hypothesis is `nunit : IsUnit (Nat.card H : A)`.  The H-action on the
group completion is `eAct`; equivariance on the unit subgroup is `eAct_unit`, and
triviality of the induced action on `L` is `hqact`.  The exact sequence
`0 → Aˣ → E → L → 0` is rendered by `q`, `i`, `hinj`, `hq`, and `hqsurj`, where
`hq` says `q e = 1 ↔ ∃ a, i a = e`; this avoids imposing an additive zero on the
multiplicative group `Multiplicative L`.  The section is `s₀`, with section equation
`hs₀`; its positivity is `hpos`.

The conclusion gives a section `s : Multiplicative L →* Algebra.GrothendieckGroup M`
and an additive character
`χ : TensorProduct ℤ (Additive (Abelianization H)) L →+
Additive (rootsOfUnity (Nat.card H) A)`.  The first conjunct is the section equation
`q.comp s = MonoidHom.id (Multiplicative L)`; the next is positivity of `s`.
The following conjunct is the clause-by-clause action formula, using
`TensorProduct.tmul ℤ (Additive.ofMul (Abelianization.of h)) ℓ` and the canonical
unit embedding `i`; `Multiplicative.toAdd.symm ℓ` identifies the additive lattice
with its multiplicative copy.  The final conjunct says every root in
`rootsOfUnity (Nat.card H) A` is fixed by every `ρ h`, exactly the stated fixed-root
clause.

The statement dependencies used are:

- `def-weil-pbc-henselian-terminology`: `IsStrictlyHenselianLocalRing` from
  `WeilConjectures.Mathlib.RingTheory.Henselian` (imported directly).
- `def-trf-fs-log-blowup`: `AlgebraicGeometry.IsFineSaturatedMonoid`, defined in
  `Sheaf.AlgebraicGeometry.LogRegularPair` and re-exported through the recorded
  dependency module `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`.

I checked the edge cases `H` trivial (so `Nat.card H = 1`), `L = 0`, the one-element
positive monoid, `n = 1`, and a monoid whose unit subgroup is all of `M`; the signature
still has the same exact-sequence and positivity clauses in each case.  No nonempty
or nonzero hypothesis was added.

Searches for an existing declaration were run as follows.  `msearch.py ... leanfinder
"finite tame group action on a strictly henselian local ring equivariant splitting of a
unit extension character roots of unity"` returned cyclotomic/Frobenius and Kummer
results but no matching theorem.  `msearch.py ... loogle "Abelianization TensorProduct
rootsOfUnity Henselian"` returned no usable match (the service reported an application
type mismatch for `TensorProduct`).  `msearch.py ... grep
"tame.*unit.*extension|rootsOfUnity|Abelianization" Mathlib/RingTheory` returned
no hits (the saved query used that subdirectory verbatim).  Direct `rg` searches of both
`WeilConjectures/` and `lean/Sheaf/` found only the parent reference in
`VeryTameEquivariantSharpChart.lean`, not a declaration of this statement.

No `STATEMENT-DISPUTED` flag or node fault was found.  No new definition node and no
dependency module were needed.

## Second reading by Q97

The resumed self-check found two errors in the saved Lean conclusion despite its
passing dry run: the section equation for `s` was absent and the action formula
omitted its final factor `s(ℓ)`. Both are repaired, without changing the node's
natural-language statement. For example, with a trivial group and a nonzero lattice,
the old action equation would force `s(ℓ) = 1`; this is incompatible with a section,
which made the paired omissions particularly important to correct.

I compared each hypothesis again: strictly henselian `A`; finite `H`; its ring action
`ρ` and identity residue action `hres`; commutative `M` and `unitEquiv`; free finite
lattice `L`; its fs, sharp, generating `Lplus`; invertible group order `nunit`;
action `eAct` compatible with ring units by `eAct_unit`; the canonical unit inclusion
`i` identified by `hi`; and exactness by `hinj`, `hq`, `hqsurj`. The quotient action is
trivial by `hqact`; `s₀`, `hs₀`, `hpos` give precisely the initially positive section.
Ring automorphisms of a local ring preserve its maximal ideal, so no separate local
morphism hypothesis is needed.

The repaired conclusion now explicitly requires `q.comp s = MonoidHom.id _`, positivity
of `s`, the homomorphism `χ` on the abelianization tensor lattice, the equality
`eAct h (s ℓ) = i (χ (h ⊗ ℓ)) * s ℓ` with the displayed additive/multiplicative
conversions, and fixedness of every root of unity. In particular the case `H = 1`
now says `s ℓ = 1 * s ℓ`, as required, while retaining the section condition. The
zero lattice, trivial positive monoid, and noncancellative `M` cases remain covered;
positivity means membership in the canonical image of `M` in its group completion.

I added the non-public proof imports
`WeilConjectures.RingTheory.HenselianLocalRootLifting`
(`IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting`) and
`Mathlib.RingTheory.Henselian`
(`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`), and expanded the proof docstring
to match all seven current DAG steps. The upstream root-lifting signature was read
with `scompile.py --source`; the two statement dependencies and their source
declarations were reread. No new node, dependency repair, or node correction is needed.

Validation: the repaired module compiled cleanly with `scompile.py`; only the
expected postponed proof remains. The node copy differs from the current shared
node only in `lean`, whose statement is the exact multiline signature from the file.
