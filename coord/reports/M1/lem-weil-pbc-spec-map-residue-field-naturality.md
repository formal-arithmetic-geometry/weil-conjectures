## Worker report

The module `Sheaf.Paper.SpecMapResidueFieldNaturality` states
`AlgebraicGeometry.spec_map_residue_field_naturality`. It binds commutative rings
`R,S : Type u`, a ring homomorphism `ψ : R →+* S`, and a prime
`p' : PrimeSpectrum S`. The first conjunct is rendered by
`Spec.map (CommRingCat.ofHom ψ) p' = PrimeSpectrum.comap ψ p'`, expressing the
point inverse-image clause. The second conjunct uses the scheme residue-field
map `(Spec.map (CommRingCat.ofHom ψ)).residueFieldMap p'`, the affine
identifications `Scheme.Spec.residueFieldIso (CommRingCat.of R) ...` and
`Scheme.Spec.residueFieldIso (CommRingCat.of S) p'`, and the prime-residue-field
map `Ideal.ResidueField.map (p'.asIdeal.comap ψ) p'.asIdeal ψ rfl`, with the
commutative equality expressed as composition in `CommRingCat`.

The dependency declarations used are Mathlib's `AlgebraicGeometry.Spec` and
`Spec.map` from `Mathlib.AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.Scheme.residueField` and
`Scheme.Hom.residueFieldMap` from `Mathlib.AlgebraicGeometry.ResidueField`,
`Localization.AtPrime` and `Ideal.ResidueField` from
`Mathlib.RingTheory.Localization.AtPrime.Basic`, and the recorded Mathlib
identifications `Scheme.Spec.residueFieldIso` and its associated residue-field
construction. The dependency node `lem-weil-pbc-spec-residue-field-identification`
has these Mathlib declarations as its `mathlib_match`.

Edge cases checked: arbitrary commutative rings (including the zero ring),
all primes of `S`, and the induced comap prime; no finiteness, nonzero, or
field hypotheses are introduced. Universes use one explicit `u` for rings and
spectrum points.

Searches for an existing exact statement used the node's recorded LeanSearch,
LeanFinder, Loogle, and grep searches (all dated 2026-10-10); they found the
stalk-level naturality lemmas but no compatibility theorem between
`Scheme.Hom.residueFieldMap` and `Ideal.ResidueField.map` through
`Scheme.Spec.residueFieldIso`. Grep of Mathlib and `WeilConjectures/` likewise
found no declaration of this theorem.

## Earlier second reading (a previous round; superseded)

Reading the node and file clause by clause: the binders match `ψ : R → R'`
and `p'` prime; the first conjunct is exactly the stated point map. The second
conjunct has the source residue-field map on the left, followed by `e_{R'}`,
and the prime-residue-field map on the right, preceded by `e_R`, so it is
exactly `e_{R'} ∘ r = κ(ψ) ∘ e_R` in categorical composition order. No
hypothesis or conclusion was added or omitted.

## Second reading by M1

I read the sandbox node, its original module, all four statement-dependency
nodes, and the actual Mathlib and upstream declarations. I read Stacks
`schemes.tex` at `lemma-spec-sheaves` (01HV(6)),
`lemma-morphism-into-affine-where-point-goes` (01HY), and `algebra.tex`'s local
rings paragraph describing the induced map on prime residue fields. The local
repository does not contain the literature checkout; the TeX was read from
`/home/ubuntu/c1-stacks-review/`. The source assumes arbitrary commutative
rings here, not fields, Noetherian rings, or finite-type homomorphisms. The
residue-field passage follows from the local stalk map; as the node correctly
notes, 01HY does not explicitly state that passage.

Objects, hypotheses, and conclusions, matched individually:

1. Arbitrary commutative rings R and R': upstream `{R S : CommRingCat.{u}}`.
   The bundled rings carry exactly the commutative-ring structure; verdict exact.
2. A ring homomorphism ψ: upstream `(φ : R ⟶ S)`, whose underlying map is
   `φ.hom : R →+* S`. No algebra, locality, injectivity, or finiteness hypothesis
   is imposed; verdict exact.
3. The affine schemes and induced morphism: `Spec R`, `Spec S`, `Spec.map φ`.
   I opened `def-weil-affine-spectrum` and `Scheme.lean`'s definitions of `Spec`
   and `Spec.map`; these are the recorded dependency notions; verdict exact.
4. A prime p' of R': upstream `(x : Spec S)` is a `PrimeSpectrum S` point,
   with prime ideal `x.asIdeal`. Its inverse image p is
   `PrimeSpectrum.comap φ.hom x`, with ideal `x.asIdeal.comap φ.hom`.
   `Spec.map_apply` identifies this with `(Spec.map φ) x` definitionally;
   verdict exact, no extra primality assumption.
5. Clause (1), the map on points: `AlgebraicGeometry.Spec.map_apply` says
   `(Spec.map φ) x = PrimeSpectrum.comap φ.hom x`; verdict exact.
6. Scheme residue fields and r: `(Spec R).residueField ((Spec.map φ) x)`,
   `(Spec S).residueField x`, and `(Spec.map φ).residueFieldMap x`.
   I opened `def-weil-residue-field` and `ResidueField.lean`: these are the
   quotient of the stalk by its maximal ideal and the induced stalk-map
   quotient homomorphism, not a replacement field; verdict exact.
7. Prime residue fields and κ(ψ): `x.asIdeal.ResidueField` and the residue
   field of `x.asIdeal.comap φ.hom`, with `Ideal.ResidueField.map _ x.asIdeal
   φ.hom rfl`. I opened `def-weil-pbc-localization-at-prime`,
   `Localization.AtPrime`, and `Ideal.ResidueField.map` (Ideal.lean:33–40).
   The latter is the residue-field map of `Localization.localRingHom`, so it
   sends fractions by ψ as the node requires; verdict exact.
8. Canonical identifications e_R and e_R': `Scheme.Spec.residueFieldIso R
   ((Spec.map φ) x)` and `Scheme.Spec.residueFieldIso S x`. I opened
   `lem-weil-pbc-spec-residue-field-identification` and all three declarations
   in its Mathlib match. The isomorphism is built by applying residue fields
   to `Spec.stalkIso`, and `algebraMap_residueFieldIso_inv` gives exactly the
   prescribed germ/residue compatibility; verdict exact, not arbitrary
   isomorphisms.
9. Clause (2): upstream `AlgebraicGeometry.Spec.residueFieldMap_residueFieldIso_hom`
   says `r ≫ e_R'.hom = e_R.hom ≫ κ(ψ)`, exactly
   `e_R' ∘ r = κ(ψ) ∘ e_R`. Its binders precede the equation in the required
   order and its p is definitionally the inverse-image prime; verdict exact.

Edge cases: the zero ring is allowed; when S is the zero ring there is no
prime x, so the statement has no excluded empty-spectrum case. No nonempty
spectrum, characteristic, reducedness, integral-domain, or finiteness assumption
is added. Fields and identity homomorphisms are included. There is no index
set or n parameter. Universe u is explicit and arbitrary, matching the scheme
and ring categories; rings initially in differing universes can both be viewed
in their common maximum universe. No test-object quantifier becomes vacuous.

Independent searches: I ran the launcher's Loogle search `"residueFieldIso"`
(12 hits: the canonical isomorphism, germ/residue compatibility, and the
field-only special case, but no general naturality statement). I ran LeanFinder
`compatibility of affine spectrum residue field homomorphism with localization
quotient under a ring morphism` (8 hits, including `Ideal.ResidueField.map_algebraMap`
and `Hom.SpecMap_residueFieldMap_fromSpecResidueField`, neither the full square).
I attempted LeanSearch `affine scheme morphism compatibility residue field
isomorphism localization quotient`; the service returned Internal Server Error
and was recorded unavailable, with no mathematical verdict inferred.
I independently searched `residueFieldIso`, `residue_field_naturality`, and the
node id in Mathlib, the project's `lean/Sheaf`, the upstream
`WeilConjectures/`, and `dag/lean_names_upstream.json`. The decisive upstream
hit was `WeilConjectures/AlgebraicGeometry/Sites/EtaleTopologicalInvariance/PropertyC.lean`
lines 38–53. I opened its section binders and proof; there are no hidden
universal-homeomorphism hypotheses from the subsequent section. No other DAG
node records this declaration. Mathlib's `Spec.map_apply` gives clause (1).

Mismatch found and repaired: H4, the first worker duplicated an existing exact
upstream statement and missed it in the search report. I removed the sandbox
module and replaced only the node's `lean` record with `existing: true`, the
upstream naturality declaration as primary, and `Spec.map_apply` as the second
recorded declaration. The note explicitly assigns one declaration to each
clause and names both source modules. `lean.statement` is copied verbatim from
the primary declaration, whose section binders are documented in the note.
The mathematical signature of the removed module was correct. There is no
statement correction, new definition node, or dependency module; no node
statement or dependency list changed. The removed module also compressed the
three proof steps to two sentences and lacked the example's copyright header;
these defects disappear when the duplicate module is dropped. Existing source
docstrings were left untouched, and no new theorem or definition was proved.

Server validation: `scompile.py` compiled scratchpad/Check.lean importing the
upstream module, printed both full signatures, and ran `#print axioms` on the
naturality theorem. Compilation was clean (1.8 seconds), and the only axioms
were `propext`, `Classical.choice`, and `Quot.sound`. All bound variables and
universe parameters are explicit in those printed signatures. No delivered
Lean module remains to compile.
