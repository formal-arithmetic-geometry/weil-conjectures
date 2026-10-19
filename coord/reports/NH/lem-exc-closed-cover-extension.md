## Worker report

Existing declaration, no new Lean module:
`AlgebraicGeometry.exists_ofArrows_closedLiftCover_mem_proetalePrecoverage`, in
`WeilConjectures.AlgebraicGeometry.ProEtale.ClosedCoverExtension` (slopmaster2).
I read the full module, including `closedLiftCoverObj`, `closedLiftCoverHom`,
the theorem's complete variable context, statement, docstring and proof. The
published source returned by `scompile.py --source` agrees with the local source.
The module and theorem explicitly identify blueprint
`lem-exc-closed-cover-extension` and realize its five-step proof. This records
an existing statement; it does not assert that its transitive proof is closed.

Hypotheses and clauses, matched individually:

- Affine W: `{B : Type u} [CommRing B]`, with `W = Spec (.of B)`. Every affine
  scheme has this presentation, with no reducedness or nonzero-ring condition.
- Closed subscheme Z_W: `(J : Ideal B)`, with `Z_W = Spec (.of (B ⧸ J))` and
  its quotient-induced closed immersion into W. This is the affine description
  of the recorded `IsClosedImmersion`, and its image is `PrimeSpectrum.zeroLocus
  (J : Set B)`. No special condition on J is assumed.
- Quasi-compact complement: `(hJ : IsCompact (PrimeSpectrum.zeroLocus
  (J : Set B))ᶜ)`. Here `IsCompact` is quasi-compactness without separation.
- Finite given family: `{ι : Type u}` and `[Finite ι]`, with `(C : ι → Type u)`
  and `[∀ a, CommRing (C a)]`; its sources are `Spec (.of (C a))`.
- The given maps to Z_W: `[∀ a, Algebra (B ⧸ J) (C a)]`. The accompanying
  B-algebra structures and `[∀ a, IsScalarTower B (B ⧸ J) (C a)]` encode
  their composites with B → B/J; these are compatible coordinate data, not an
  additional geometric restriction.
- Ind-etale: `[∀ a, Algebra.IndEtale (B ⧸ J) (C a)]`. This is exactly the affine
  ind-etale basis, rather than arbitrary weakly etale sources.
- Covering: `hC` says every prime of B/J is in the image of one of these spectrum
  maps. For a finite family of affine sources over an affine target this is
  equivalent to the full pro-etale precoverage condition: all maps are weakly
  etale, hence flat, and affine, hence quasi-compact. Above every affine open
  of the target their inverse images are affine, and this finite family covers
  it. Thus joint surjectivity here does not silently replace an fpqc condition
  for a family for which that condition could fail.
- The finite extension: `∃ (κ : Type u) (_ : Finite κ) (f : κ → B), ...` and
  `Presieve.ofArrows _ (closedLiftCoverHom C f) ∈ Scheme.proetalePrecoverage
  (Spec (.of B))`. Its index set is `ι ⊕ κ`, finite because both parts are finite.
  This is membership in the actual pro-etale precoverage, including fpqc.
- Members above the closed fibre: `closedLiftCoverObj C f (.inl a)` is
  `Spec (.of (Algebra.ClosedLift B (C a)))`, with the structure map specified by
  `closedLiftCoverHom`. This is exactly H_B(C_a), used by the recorded
  `Scheme.AffineProEt.closedSiteLift`; that functor uses global-section
  coordinates for an arbitrary affine object, canonically isomorphic to C_a.
  It is the same construction, not an arbitrary lift or map.
- Other members: the `.inr b` objects are
  `Spec (.of (Localization.Away (f b)))`, with their localization maps. These
  identify with the affine open D(f_b). The conclusion `∀ b, f b ∈ J` puts
  every such open in W minus Z_W. The displayed union equality gives the
  explicit standard-open realization of the complementary members used in
  Step 1 of the blueprint proof.
- Reduction of each lifted member: `∀ a, Function.Bijective
  (Algebra.ClosedLift.reduction B (C a) J)`. This is the specified ring map
  H_B(C_a)/JH_B(C_a) → C_a. Bijectivity gives a ring isomorphism and therefore
  precisely the closed-base-change isomorphism to V_a over Spec(B/J), by the
  affine fibre-product and quotient tensor formulas. It does not merely state
  the existence of an unrelated isomorphic object.
- Reduction of every complementary member: `∀ b, Subsingleton
  (Localization.Away (f b) ⧸ J.map (algebraMap B (Localization.Away (f b))))`.
  The base-change ring is the zero ring, so its spectrum is empty. This is the
  required empty reduction, not vanishing of an unrelated object.

Dependency declarations read and used to check this match:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, together with `IsCompact` on
  the complement as a subset of the underlying spectrum.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.proetalePrecoverage`; this dependency has status
  mathlib and its `mathlib_match` is its usable declaration record.
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`:
  `AlgebraicGeometry.Scheme.AffineProEt`, its inclusion `toProEt`,
  `precoverage`, and `topology`. The full signature and definitions identify
  its affine ind-etale objects and the induced covering notion.
- `Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift`:
  `AlgebraicGeometry.Scheme.AffineProEt.closedSiteLift`, together with
  `closedSiteLiftObj` and `closedSiteCoordinates`; its imported
  `Sheaf.RingTheory.ProEtale.ClosedLiftMap` uses the existing
  `WeilConjectures.RingTheory.ProEtale.ClosedLift` construction without redefining it.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`.

Edge cases checked: J = 0 (empty complement, κ can be empty); J = top
(empty closed subscheme, the given family can be empty); the zero base ring
(empty W); empty sources in the given cover; arbitrary nonreduced rings and
ideals; and a finite empty index set. No Nonempty or Nontrivial instance is
assumed by the theorem. The common universe u for finite index sets and rings
loses no finite family: any finite set can be reindexed in that universe, and
u is arbitrary. No field, characteristic, Noetherian or finite-type hypothesis
appears. No statement correction, missing notion, dependency repair, or
STATEMENT-DISPUTED fault was found.

Searches made (2026-10-16):

- `msearch.py leanfinder`, query: "A finite affine ind etale covering of a closed
  subscheme extends to a finite pro etale covering of an affine scheme using
  closed lifts and complementary affine opens". Eight Mathlib hits concerning
  affine covers and affine transition limits; none is this closed-lift extension.
- `msearch.py loogle`, query `"proetale"`. Twelve results including
  `Scheme.proetalePrecoverage`, its topology and stability instances, and
  comparisons with etale and fpqc topology. These give the covering definition,
  not the extension theorem.
- `msearch.py leansearch`, query: "A finite affine ind-etale cover of a closed
  subscheme extends by closed-site lifts and affine opens to a pro-etale cover
  of an affine scheme". Service unavailable: Internal Server Error. This is
  recorded as unavailable, not evidence of absence.
- `msearch.py grep`, query `closedLift|closedSiteLift|closed_cover`, subdirectory
  `AlgebraicGeometry`: no Mathlib matches.
- `rg` in `WeilConjectures/AlgebraicGeometry` and the project's
  `lean/Sheaf/AlgebraicGeometry/ProEtale`, query
  `closed.cover|closedLiftCover|closedSiteLift|lem-exc-closed-cover-extension`:
  found the exact upstream module `ClosedCoverExtension.lean`, including its
  blueprint attribution, two family constructions and the theorem. Side results
  were the recorded closed-site lift, adjunction and functor properties, not a
  competing extension theorem.
- Direct blueprint-id search in upstream source found the theorem's explicit
  `lem-exc-closed-cover-extension` documentation. Searches of the upstream-name
  index produced no additional match. The actual source signature and the
  published server source, rather than the name index, establish the match.

Only the item's `lean` field is changed. The signature in that record is copied
verbatim from the existing theorem; its section-variable context is listed above.
No new `.lean` file is delivered, in accordance with the one-definition rule.


## Second reading by NH

I did not write the worker's record. I independently opened the sandbox node,
its unchanged shared-DAG statement and five proof steps, and the entire existing
`WeilConjectures.AlgebraicGeometry.ProEtale.ClosedCoverExtension` module. I read
its section variables as well as the theorem beginning at line 62, both family
constructions and the proof. `scompile.py --source` with the full module name
returned the current published source: its signature is verbatim identical to
`lean.statement`. The older source checkout has the same statement; the current group-clone
source and the published source are authoritative for this review.

Source reading: the local launcher literature mirror contains the actual
blueprint `sec-smooth-purity/sk-prop-sf-closed-unit/lem-exc-closed-cover-extension.md`,
order 1854, which I read in full. Its statement is exactly the node's statement.
I also read `proetale.tex`, Section `section-ind-etale`, Tag 097P
(`lemma-lift-ind-etale`), and Section `section-closed-immersion`, Tag 09BK
(`lemma-closed-immersion-affines`), including their proofs and introductory
context. They use arbitrary commutative rings and ideals, and the canonical
colimit over etale factorizations; there is no background field, Noetherian,
finite-type, reducedness or nonzero-ring assumption. The source of the covering
notion is Tag 0989 (`definition-fpqc-covering`), read in the same TeX source.
I checked the quotient description of affine closed immersions against Tag
01QO. The public source links are [097P](https://stacks.math.columbia.edu/tag/097P),
[09BK](https://stacks.math.columbia.edu/tag/09BK),
[0989](https://stacks.math.columbia.edu/tag/0989), and
[01QO](https://stacks.math.columbia.edu/tag/01QO).

My object/hypothesis/conclusion checklist, with the actual Lean rendering:

1. An arbitrary affine scheme W. `{B : Type u} [CommRing B]` and
   `Spec (.of B)` give affine coordinates, as permitted by
   `def-pc-scheme` and `def-weil-affine-spectrum`. Verdict: same object up to
   its affine presentation, with no hypothesis on B beyond a commutative ring.
2. A closed subscheme Z_W of W. `(J : Ideal B)` gives
   `Spec (.of (B ⧸ J))` and the quotient-induced morphism to `Spec (.of B)`.
   The affine equivalence in `def-weil-closed-immersion` identifies every
   affine closed immersion with precisely such data. Its underlying subset
   is `PrimeSpectrum.zeroLocus (J : Set B)`. Verdict: general affine closed
   subscheme, with its scheme structure retained, not just its closed subset.
3. The complement is quasi-compact.
   `hJ : IsCompact (PrimeSpectrum.zeroLocus (J : Set B))ᶜ` expresses compactness
   of the complementary subspace. I opened `IsCompact` and `CompactSpace`:
   neither includes a separation condition. Verdict: exact hypothesis.
4. A finite family of affine sources V_a, with maps to Z_W.
   `{ι : Type u}`, `[Finite ι]`, `C : ι → Type u`, and
   `[∀ a, CommRing (C a)]` give the sources `Spec (.of (C a))`.
   `[∀ a, Algebra (B ⧸ J) (C a)]` gives their structural maps.
   The section also binds `[∀ a, Algebra B (C a)]` and
   `[∀ a, IsScalarTower B (B ⧸ J) (C a)]`: the former is the composite
   B-algebra structure and the latter says it is that composite. These data
   can always be supplied from the quotient-algebra maps. Verdict: no extra
   geometric hypothesis and no arbitrary choice of structural morphisms.
5. Each given source is ind-etale over Z_W.
   `[∀ a, Algebra.IndEtale (B ⧸ J) (C a)]` uses the existing filtered-colimit
   notion from `WeilConjectures.RingTheory.ProEtale.IndEtale`, read at its class
   declaration. This is over B/J, not over B. Verdict: exact hypothesis.
6. The given family covers Z_W. `hC` quantifies over every
   `p : PrimeSpectrum (B ⧸ J)` and requires some a with p in the range of the
   induced comap. This is joint surjectivity. In this finite affine family it
   is equivalent to the whole covering condition: ind-etale implies weakly
   etale, and each morphism between affine schemes is affine. Over any affine
   target open E, the inverse images of E are affine opens, finitely many,
   and cover E. Conversely Tag 0989 implies joint surjectivity. Verdict: no
   fpqc hypothesis is lost; this equivalence is specific to the finite affine
   setting and is not asserted for arbitrary weakly etale families.
7. A finite extension exists. `∃ (κ : Type u) (_ : Finite κ) (f : κ → B)`
   supplies the other indices. The resulting index is `ι ⊕ κ`, finite from
   the two finite types. It is chosen after all original family data and
   hypotheses. Verdict: correct finiteness and quantifier order.
8. Its members over the closed fibre are v_W(V_a).
   `closedLiftCoverObj C f (.inl a)` is literally
   `Spec (.of (Algebra.ClosedLift B (C a)))`; `closedLiftCoverHom` supplies the
   spectrum of the structural B-algebra map. I read `Algebra.ClosedLift` as
   the real colimit of the etale factorizations, and opened the dependency
   `closedSiteLift`, its object and coordinate definitions. The latter uses
   Γ(V_a, top), canonically the C_a of the affine presentation, and the same
   colimit construction. Verdict: the specified canonical lift, up to the
   usual canonical coordinate isomorphism, not an arbitrary isomorphic lift.
9. The other members are affine opens in W minus Z_W.
   `closedLiftCoverObj C f (.inr b)` is
   `Spec (.of (Localization.Away (f b)))`, and its morphism is the localization
   map. This is D(f_b); `(∀ b, f b ∈ J)` places it in the complement.
   The union equality explicitly chooses these opens to cover the complement.
   Verdict: exactly the standard-open realization prescribed by the source
   proof. Choosing principal opens covering the complement is available from
   the existing quasi-compactness hypothesis, not an added assumption or a
   restriction on the given V_a.
10. The entire family is a pro-etale covering of W.
    `Presieve.ofArrows _ (closedLiftCoverHom C f) ∈
    Scheme.proetalePrecoverage (Spec (.of B))` uses Mathlib's actual covering
    definition, not just a generated covering sieve or joint surjectivity.
    I opened `proetalePrecoverage = propQCPrecoverage @WeaklyEtale`; its
    quasi-compact covering clause supplies the fpqc finite-open condition.
    Verdict: full conclusion, with both weak etaleness and fpqc coverage.
11. The closed reductions of the lifts are the original V_a.
    `∀ a, Function.Bijective (Algebra.ClosedLift.reduction B (C a) J)` concerns
    the specified map `H_B(C_a)/JH_B(C_a) → C_a`, read in `ClosedLift.lean`.
    Bijectivity makes it a ring isomorphism; its B/J-linearity follows from
    its definition as the quotient of the structural algebra map. The affine
    fibre-product/quotient-tensor identifications give exactly the isomorphism
    over Z_W of the node. Verdict: correct reduction map and base, not a bare
    unrelated ring equivalence.
12. The reductions of the other members are empty.
    `∀ b, Subsingleton (Localization.Away (f b) ⧸
    J.map (algebraMap B (Localization.Away (f b))))` says their closed-fibre
    coordinate rings are zero rings. These are exactly the quotient rings of
    the closed base changes, so their spectra are empty. Verdict: exact clause.

Dependency-interface reading: I opened all eight statement-dependency records.
For scheme, spectrum, closed immersion, compactness and pullback I opened the
recorded Mathlib declarations, not similarly named project notions. I read the
full `ClosedSiteLift.lean` dependency module and `ClosedLiftMap.lean`'s imported
construction through `Algebra.ClosedLift`. I opened `AffineProEt`, `toProEt`,
its `precoverage` and `topology`: the basis consists of affine ind-etale objects
and its covers come from the pro-etale precoverage. The covering dependency has
no `lean` field but has the usable Mathlib match `Scheme.proetalePrecoverage`;
its actual definition agrees with the node. `pullback`, `pullback.fst` and
`pullback.snd` supply the standard fibre product. None of these interfaces
requires an unprovided instance or forces a different notion. There are no
new nodes or dependency modules in this delivery, hence no H12/H13 repair.

Edge cases: ι may be empty; then hC precisely forces the closed spectrum to be
empty. J = 0 gives empty complement and allows κ empty. J = top gives empty
closed fibre and allows an empty original covering. B may be the zero ring;
all relevant spectra are then empty, and the compactness and covering
conditions still make sense. Any C_a may be zero. No `Nonempty`, `Nontrivial`,
characteristic, Noetherian, finite-generation or finite-type premise occurs.
There is no cohomological n in this statement; the zero-size family plays the
n = 0 role in the covering definition. The arbitrary universe u bounds rings
and schemes in the usual common universe; any finite collection of rings can
be placed in one common upper universe, and any finite index type reindexed
there. No independent smaller test universe makes a premise vacuous. Every
variable in the recorded signature is bound in the existing declaration's
section context, which the server's full `#check @...` probe verifies.

Independent duplicate searches (2026-10-16), using alternative descriptions:

- `msearch.py leanfinder`: “Extend jointly surjective finite ind-étale algebras
  over B/I by canonical étale neighbourhood lifts and localizations to cover
  Spec B”. Eight hits, chiefly `Algebra.exists_etale_of_isEtaleAt`, standard
  etale algebra, etale loci and localization properties; none states this
  covering extension with canonical lifts and reductions.
- `msearch.py loogle`: `"closedLiftCover"`. Zero Mathlib hits.
- `msearch.py grep`: `ClosedLift|closedLiftCover|closedSiteLift|quotient.*cover`,
  subdirectory `AlgebraicGeometry`. Zero Mathlib hits.
- `msearch.py leansearch`: “Lift a finite ind etale covering along an affine
  closed immersion and add finitely many standard opens of the complement”.
  Service returned Internal Server Error; recorded as unavailable, not as
  evidence of absence.
- Direct `rg` across upstream `WeilConjectures` and project `lean/Sheaf`, using
  `lem-exc-closed-cover-extension|closedLiftCover|cover.*[Cc]losed|[Cc]losed.*cover`,
  finds the exact existing `ClosedCoverExtension` theorem, its family data,
  the upstream closed-lift module, and unrelated closed-cover statements.
  The small-site closed-lift declarations are the dependency construction,
  not a second extension theorem. Searching the current group-clone upstream
  sources also finds the same theorem and signature.

H5-H9: this is an existing-declaration record, so no new definition, proof or
module is introduced or edited. The existing colimit/localization definitions
have real data. The upstream theorem documentation names the blueprint and
explains compactness selection, lifts and reductions, coverage and weak
etaleness; its actual proof separately checks `QuasiCompactCover`, rather
than assuming surjectivity alone suffices. The DAG's five-step natural-language
proof remains available verbatim for stage 3. Its source's documentation is
not reformatted into the new-module template, because the one-definition rule
requires recording the already published theorem. No proof-closure claim is
made: its two named open closed-lift prerequisites remain open.

Mismatches found and changes: none in the statement, dependency interfaces or
recorded signature. I retained the worker's complete `lean` record and added
this independent second reading only. No statement correction or citer audit
is needed. The required delivery dry run compiles an import and full `#check`
for the existing theorem and both family constructions; no new Lean files
need compilation.

Validation: `deliver2.py NH lem-exc-closed-cover-extension --no-push` printed
`OK (dry run)` on 2026-10-16: the existing-declaration probe compiles cleanly
and the current-server preflight passes. The packet contains only the item
node record and this report.
