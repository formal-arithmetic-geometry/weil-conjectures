## Worker report

The module states the Stacks Project Lemma 07DT (part (3), “if” direction) for a
ring homomorphism `f : R →+* S`. The binders `[CommRing R]` and `[CommRing S]`
render the hypothesis that the rings are commutative. The typeclass
`[IsArtinianRing S]` renders that `S` is Artinian, and `[IsLocalRing S]` renders
that it is local. Mathlib's `IsLocalRing.ResidueField S` is the quotient
`S / maximalIdeal S`, and `IsLocalRing.residue S` is its quotient map. Thus
`(IsLocalRing.residue S).comp f` is exactly the composite `R → S → S/𝔪` in the
node. The hypothesis `h` says this composite is essentially of finite type, via
`RingHom.EssFiniteType`; the conclusion `f.EssFiniteType` says `R → S` is
essentially of finite type. The proof is intentionally `sorry` at stage 2.

The only imported notions are Mathlib's `IsArtinianRing`, `IsLocalRing`,
`IsLocalRing.ResidueField`, `IsLocalRing.residue`, and
`RingHom.EssFiniteType`; no dependency module is needed because the sole
statement dependency `def-weil-pbc-essentially-finite-type-algebra` is the
Mathlib declaration `Algebra.EssFiniteType` (and its ring-hom algebraization).

Edge cases checked: the maximal ideal is allowed to be zero (the field case),
`S/𝔪` is therefore still the correct residue field; no nontriviality or
Noetherian hypothesis was added; arbitrary commutative rings `R` and `S` are
allowed; and the statement does not exclude zero or characteristic-
`p` rings beyond whatever the Artinian-local hypotheses entail.

Searches for an existing declaration: `msearch.py leanfinder` query “Artinian
local ring essentially of finite type if residue field is essentially of finite
type” found only unrelated `EssFiniteType` and residue-field results; `msearch.py
loogle` query `RingHom.EssFiniteType IsArtinianRing IsLocalRing` found no theorem
with this implication; `msearch.py grep` and `rg` over Mathlib, WeilConjectures,
and `lean/Sheaf` found no matching theorem. The dependency's recorded
Mathlib match, `Algebra.EssFiniteType` in
`Mathlib/RingTheory/EssentialFiniteness.lean`, was read and used through
`RingHom.EssFiniteType`.

## Earlier second reading (a previous round; superseded)

Reading the node and the module side by side: `R → S` is represented by `f`,
commutativity by both `CommRing` binders, Artinian and local by the two S
instances, and the named maximal ideal quotient by Mathlib's canonical
`ResidueField S` and `residue S`. The composite is formed in the stated order
with `.comp f`; the hypothesis and conclusion are exactly the two essentially
finite type assertions. No hypothesis or conclusion clause is missing, and no
special case or extra assumption is present.

## Second reading by H1

The node introduces a homomorphism of commutative rings `R → S`; Lean renders
this as `R S : Type*`, `[CommRing R]`, `[CommRing S]`, and `f : R →+* S`.
It assumes that `S` is Artinian and local; these are exactly the typeclasses
`[IsArtinianRing S]` and `[IsLocalRing S]`.  The node's maximal ideal and
residue quotient `S/𝔪` are rendered by Mathlib's canonical
`IsLocalRing.ResidueField S` and quotient map `IsLocalRing.residue S`.
Consequently the hypothesis that `R → S/𝔪` is essentially of finite type is
exactly `(IsLocalRing.residue S).comp f |>.EssFiniteType`.  The conclusion that
`R → S` is essentially of finite type is exactly `f.EssFiniteType`.  The
quantifier order and all hypotheses and conclusion clauses agree; no extra
Noetherian, nontriviality, finiteness, characteristic, or universe restriction
is present.

Edge cases were checked: the maximal ideal may be zero (the field case), the
residue quotient remains the canonical residue field, zero or positive
characteristic rings are permitted whenever the Artinian-local classes exist,
and arbitrary types `Type*` are allowed.  Empty index sets and `n = 0` do not
occur in this statement.

I searched with `msearch.py` LeanFinder and Loogle queries for the Artinian-local
residue implication, and with `rg` through Mathlib, `WeilConjectures`, and
`lean/Sheaf`; only the general `EssFiniteType` and residue-field declarations
were found, so this is a new statement.  The recorded dependency is the
Mathlib essentially-finite-type notion and is usable as recorded.

The module was compiled with `scompile.py`; it compiles cleanly with only the
intentional `sorry`.  No mismatch was found and no source or Lean statement
was changed.
