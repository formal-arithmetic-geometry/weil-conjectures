## Worker report

The item is stated by `AlgebraicGeometry.Scheme.Modules.exists_sectionRing_proj_morphism`
in `Sheaf.AlgebraicGeometry.AmpleProjCanonicalMap`. It has only a `sorry` proof.
A sibling module `Sheaf.AlgebraicGeometry.InvertibleSectionRing` supplies the missing actual
section ring and its grading. It specifies every operation; the only postponed parts are
named theorems asserting algebraic laws. No statement correction or dependency replacement
was necessary. The item's `stmt_deps` gains the two new definition records below.

The Stacks files are absent from this machine's literature checkout. I read the authoritative
[01PZ](https://stacks.math.columbia.edu/tag/01PZ),
[01N8](https://stacks.math.columbia.edu/tag/01N8), and
[01CY](https://stacks.math.columbia.edu/tag/01CY) pages instead. The item's existence, cover
hypothesis, inverse-image assertion and fraction formula agree with these sources.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Arbitrary scheme X: `(X : Scheme.{v})`. There is no field, no finiteness condition and no
  separatedness assumption. All universes and all implicit variables are explicitly bound.
- An invertible O_X-module: `(L : X.Modules) [L.IsInvertible]`, using exactly the dependency's
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, not a replacement predicate.
- S = direct sum of Γ(X,L^{tensor n}): `InvertibleSectionRing L` is literally
  `⨁ n : ℕ, SectionRingComponent L n`, with `SectionRingComponent L n : Type u` the carrier
  of `Γ(L.tensorPow n, ⊤)`. Addition is Mathlib's direct-sum addition. Multiplication tensors
  the sections by `tmulSection`, then applies `(L.tensorPowAddIso i j).inv.app ⊤`.
  The unit is `unitSectionsEquiv ⊤ 1`, in degree zero. Natural and integer casts are the
  corresponding multiples of that unit. The `DirectSum.GCommRing` instance contains these
  data explicitly and takes proofs from named algebraic-law theorems. `sectionRingGrade L n`
  is the additive subgroup which is the image of the nth direct-sum inclusion.
- A homogeneous section s of positive degree d: `(d : ℕ) (_hd : 0 < d)
  (s : sectionRingGrade L d)`. This is an actual subtype of S, not a bare label for an
  unrelated section. `s.val d` is its degree-d component, an actual section of L^{tensor d}.
- The nonvanishing open X_s: `generatingLocus (s.val d)`. For invertible modules this
  existing definition is exactly nonvanishing in the fibre. In a local basis e, s = c e;
  both notions say c is a unit in the local ring, or equivalently c has nonzero residue.
  `generatesAt_iff_mem_basicOpen` in the existing source makes this identification explicit.
- The cover hypothesis: `hcover : ∀ x : X, ∃ (d : ℕ) (s : sectionRingGrade L d),
  0 < d ∧ x ∈ generatingLocus (s.val d)`. This covers by all positive homogeneous sections;
  no fixed degree, finite subfamily, or affine nonvanishing hypothesis is imposed.
- Existence of the canonical scheme morphism: `∃ f : X ⟶ Proj (sectionRingGrade L), ...`.
  The conclusion specifies the canonical local maps by their values on all homogeneous
  fractions. Thus it identifies the canonical morphism, rather than merely an arbitrary
  morphism having the right point map. It need not choose a noncomputable representative.
- The inverse-image equality for every positive homogeneous s is the first conjunct:
  `f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val = generatingLocus (s.val d)`.
- On global sections of each chart: `HomogeneousLocalization.Away.mk ... s.property n
  ξ.val ξ.property` is exactly ξ/s^n, with `ξ : sectionRingGrade L (n • d)`.
  For naturals, `n • d` is n*d. `Proj.awayToSection` is the canonical identification with
  chart sections, which is an isomorphism in positive homogeneous degree; `f.app` is the
  induced ring map to sections on the inverse image. The latter open equals X_s by the
  first conjunct. Thus there is no arbitrary chart ring map substituted for the induced map.
- The image is s^{-n}ξ: the second conjunct asserts that this pulled-back scalar, multiplied
  into the restriction of `(s.val ^ n) (n • d)`, equals the restriction of `ξ.val (n • d)`.
  Both restrictions use the explicitly written inclusion
  `f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤`.
  Since the denominator section is a free generator on X_s, this equality uniquely gives
  the quotient by s^n. It is exactly the source's division formula expressed without an
  extra inverse-choice definition. Every element of the degree-zero localization has such
  a homogeneous-fraction representation (`HomogeneousLocalization.Away.mk_surjective`).

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`, read with their locally-ringed-space definitions.
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, full class and its docstring.
  The same module provides the actual `tensorPow` and `tensorPowAddIso` used here.
- `def-pc-proj`: `AlgebraicGeometry.Proj` and `AlgebraicGeometry.projIsoSpec`,
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`; `ProjectiveSpectrum.basicOpen`
  and the scheme-open wrapper `Proj.basicOpen`. The module `Basic` also supplies the used
  `Proj.awayToSection` and its positive-degree isomorphism `basicOpenIsoAway`.
- New ring node: all ring and grading declarations in
  `Sheaf.AlgebraicGeometry.InvertibleSectionRing`.
- New generating-locus record: `AlgebraicGeometry.Scheme.Modules.generatingLocus`,
  `WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus`. I read its definition,
  `GeneratesAt`, and its local coefficient and free-generator lemmas.
- Ring construction: `tmulSection` and `unitSectionsEquiv` in
  `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`; `DirectSum.GCommRing`,
  `GradedMonoid.GMonoid`, `DirectSum.IsInternal.chooseDecomposition` and `GradedRing`
  in Mathlib. The chosen decomposition is the inverse of a named bijectivity theorem;
  its underlying ring operations are never selected from an existence theorem.

Edge cases checked:

- Empty X: hcover is vacuous; the zero section ring and empty Proj are allowed. The map
  and every chart equation are well-typed on empty opens.
- s = 0 in positive degree: included as a homogeneous subtype. Its nonvanishing and Proj
  basic opens are empty; no nonzero/nonzerodivisor assumption is inserted.
- n = 0 in the fraction formula: the denominator is the section 1 in degree zero, and
  arbitrary degree-zero numerators are included. Only the section's degree d must be positive.
- Distinct positive degrees, arbitrarily large degrees and unbounded section families:
  quantified independently. No restriction to degree one is made.
- Arbitrary characteristic and nonreduced schemes: no field, domain, reducedness,
  finite-generation or torsion-free hypothesis occurs.
- Universe v is arbitrary, and the modules use their dependency's standard same-universe
  section carriers. No point, section or cover index set is restricted to be finite/countable.

The ten named ring-law theorems left with `sorry` are `sectionRing_mul_zero`,
`sectionRing_zero_mul`, `sectionRing_mul_add`, `sectionRing_add_mul`, `sectionRing_one_mul`,
`sectionRing_mul_one`, `sectionRing_mul_assoc`, `sectionRing_mul_comm`,
`sectionRing_gradedMonoid`, and `sectionRing_isInternal`. They are construction obligations
of the new definition node, with a natural-language argument in each docstring. The main
item's docstring carries all four proof steps and the proof-node citations.

Searches, performed through msearch.py plus direct read-only rg:

- leanfinder: `canonical morphism from a scheme to Proj of section ring of an invertible sheaf` — 8 hits; AlgebraicGeometry.Proj.fromOfGlobalSections, AlgebraicGeometry.Proj.toSpecZero, AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec, AlgebraicGeometry.Proj.basicOpenToSpec, AlgebraicGeometry.Proj.awayι, AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections, AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq, AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero.
- loogle: `AlgebraicGeometry.Proj.fromOfGlobalSections, AlgebraicGeometry.Scheme.Modules.IsInvertible` — 0 hits; loogle: unknown identifier 'AlgebraicGeometry.Scheme.Modules.IsInvertible'.
- grep: `sectionRing|SectionRing|section ring|fromOfGlobalSections` in `AlgebraicGeometry` — 7 hits; Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean, Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean, Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean, Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean, Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean, Mathlib/AlgebraicGeometry/Artinian.lean, Mathlib/AlgebraicGeometry/StructureSheaf.lean.
- leansearch: `section ring tensor powers invertible sheaf` — 0 hits; service unavailable: Internal Server Error.
- leanfinder: `nonvanishing open of a global section of an invertible module free generator` — 8 hits; AlgebraicGeometry.LocallyRingedSpace.Γevaluation_ne_zero_iff_mem_basicOpen, AlgebraicGeometry.Scheme.evaluation_ne_zero_iff_mem_basicOpen, AlgebraicGeometry.LocallyRingedSpace.evaluation_ne_zero_iff_mem_basicOpen, AlgebraicGeometry.RingedSpace.mem_basicOpen', AlgebraicGeometry.RingedSpace.basicOpen, AlgebraicGeometry.RingedSpace.mem_top_basicOpen, AlgebraicGeometry.RingedSpace.mem_basicOpen, AlgebraicGeometry.Scheme.mem_basicOpen'.
- loogle: `DirectSum.GCommRing, SetLike.GradedMonoid` — 1 hits; SetLike.gcommRing.
- grep: `GCommRing|GradedMonoid|SectionRing` in `Algebra/DirectSum` — 15 hits; Mathlib/Algebra/DirectSum/Algebra.lean, Mathlib/Algebra/DirectSum/Algebra.lean, Mathlib/Algebra/DirectSum/Algebra.lean, Mathlib/Algebra/DirectSum/Algebra.lean, Mathlib/Algebra/DirectSum/Algebra.lean, Mathlib/Algebra/DirectSum/Ring.lean, Mathlib/Algebra/DirectSum/Ring.lean, Mathlib/Algebra/DirectSum/Ring.lean.
- leansearch: `nonvanishing open of a section of an invertible module` — 0 hits; service unavailable: Internal Server Error.
- grep: `generatingLocus|nonvanishing` in `AlgebraicGeometry` — 0 hits; no hits.
- leanfinder: `commutative graded ring direct sum of global sections of tensor powers of an invertible module` — 8 hits; AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.commRingStructureSheafInTypeObj, AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.structurePresheafInCommRing, TensorPower.galgebra, TensorAlgebra.gradedAlgebra, AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf, TensorPower.gmonoid, GradedTensorProduct.instAddCommGroupWithOne, AlgebraicGeometry.Proj.awayToSection.

The searches found only `Proj.fromOfGlobalSections`, whose input is a ring map into
ordinary global functions. Its signature was read: it does not construct the section ring
or treat an arbitrary invertible L, so it cannot replace this theorem. TensorPower.gmonoid
and TensorPower.galgebra are for tensor powers of one module over one ring, not global
sections of sheaf tensor powers. Direct rg of Mathlib, WeilConjectures and lean/Sheaf for
`sectionRing|SectionRing|section ring|tensorPower|TensorPower` found no section-ring
construction. `rg generatingLocus|nonvanishing` located the existing generating-locus
source, which is reused. `rg` on dag/lean_names_upstream.json and the source/library trees
found no declaration-name clashes. The item id has no tagged declaration in WeilConjectures.
DAG rg found no definition node for either notion; blueprint_refs.py searches `section ring`
and `nonvanishing` both returned zero blueprint matches. Raw msearch results remain in
sandbox `searches.jsonl` and are reproduced in the new node search records.

No STATEMENT-DISPUTED or source mismatch was found. All files are sandbox files. Compilation
uses only scompile.py on the server, never a local build.

## New nodes

`def-sc-invertible-section-ring`: the actual graded section ring of an invertible module,
with tensor multiplication, degree-zero unit and summand grading, from Stacks 01PZ and
01N8. Search found existing sheaf tensor powers and tensor sections but no assembled ring.
Its sibling module supplies explicit data and named law obligations. It cites exactly
`def-pc-scheme` and `def-sc-invertible-module`.

`def-sc-section-generating-locus`: the open union of neighbourhoods where a global section
freely generates the module, and its identification with the nonvanishing open for an
invertible module (Stacks 01CY). DAG and blueprint searches found no definition node.
The source already has precisely this notion, so the record is `existing: true`, module
`WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus`, declaration
`AlgebraicGeometry.Scheme.Modules.generatingLocus`, with no duplicate module. The definition
works even for arbitrary modules; the node states that general definition before its
invertible specialization. It cites exactly `def-pc-scheme` and `def-sc-invertible-module`.

Validation: the combined sibling modules compiled cleanly on the server (about 3 seconds).
The first dry run found that the current server blueprint ancestry had grown since the
read-only checkout: both new nodes' `blueprint.from.via` were updated to the exact ancestry
reported by preflight. The item statement and its proof remain unchanged. The independent
second-reading section is deliberately reserved for the next worker, as deliver2.py requires.


## Second reading by M1

I independently opened the item, both new definition nodes, both delivery modules,
all three original statement dependencies, and their recorded Lean declarations.
The mathematical statement passes H3 without a correction. No dependency replacement
is required. The only record repair is storing the main theorem signature with the
literal newlines and indentation of the Lean file, rather than a flattened signature.
The Lean files themselves are unchanged.

Source reading: the repository has no Stacks checkout. I fetched the authoritative
Stacks source files into this item's scratchpad and read properties.tex at
`lemma-map-into-proj` (01PZ), constructions.tex at `lemma-converse-construction`
(01N8), and modules.tex at `lemma-s-open` (01CY), including the surrounding
invertible-module section and `definition-gamma-star`. The latter defines the
nonnegative section ring and its tensor multiplication. These sources impose no
base field, characteristic, Noetherian, separatedness, or finite-generation condition
on this item. The node intentionally selects existence and clause (1) of 01PZ,
with the local formula from 01N8; the other clauses of 01PZ are outside this node.
References: https://stacks.math.columbia.edu/tag/01PZ,
https://stacks.math.columbia.edu/tag/01N8,
https://stacks.math.columbia.edu/tag/01CY.

My object, hypothesis, and conclusion inventory and its Lean correspondence:

1. An arbitrary scheme X: `X : Scheme.{v}`. PASS. I read Mathlib's Scheme and Hom:
   local affine locally ringed spaces, with locally ringed-space morphisms. No
   curve or base scheme is substituted.
2. An invertible O_X-module L: `L : X.Modules` and `[L.IsInvertible]`. PASS. The
   dependency's IsInvertible requires local isomorphisms to the structure sheaf.
   This is local rank one and implies quasi-coherence, so the dependency's
   quasi-coherence wording adds no missing independent assumption.
3. S = direct sum of sections of L^{tensor n}: `InvertibleSectionRing L`, used
   through `sectionRingGrade L`. PASS. `SectionRingComponent` is exactly
   `Γ(L.tensorPow n, ⊤)`; DirectSum supplies the actual finite-support addition.
   `sectionRingGMul` applies `tmulSection` and the inverse of `tensorPowAddIso`;
   I checked that the latter's direction is L^{i+j} -> L^i tensor L^j.
   The degree-zero unit is `unitSectionsEquiv ⊤ 1`. The component subgroup is
   `DirectSum.of ... n`'s range. These are actual data, not existentially selected
   ring operations. The ten named law obligations have only sorry proofs and
   their own source/proof docstrings. Decomposition chooses only the inverse
   of a stated bijective recomposition map; it does not choose the ring data.
4. A homogeneous positive-degree s and its nonvanishing open X_s:
   `d : ℕ`, `0 < d`, `s : sectionRingGrade L d`, and
   `generatingLocus (s.val d)`. PASS. Range membership says this direct-sum
   element has only its degree-d component. Every actual section can be included
   in that range, so neither the cover nor the final quantifiers lose sections.
   I read GeneratesAt, generatingLocus, IsFreeGenerator and the local coefficient
   criterion: for an invertible module free generation means the local coefficient
   is a unit, equivalently its residue is nonzero. This is exactly 01CY's X_s.
5. The opens X_s cover X: `hcover : ∀ x : X, ∃ d s, 0 < d ∧ ...`.
   PASS. Degree and section may depend on x; there is no fixed-degree or finite
   cover assumption and no requirement that X_s be affine.
6. Existence of a canonical scheme morphism: `∃ f : X ⟶ Proj (sectionRingGrade L)`.
   PASS. The following local-map formulas specify the canonical map. They
   determine its maps into affine charts on the given cover, so existence of
   a witness satisfying them expresses the canonical construction without
   introducing an extra chosen morphism or a weaker point-map-only condition.
7. Every positive homogeneous section satisfies the inverse-image identity:
   the first conjunct is `f ⁻¹ᵁ Proj.basicOpen ... s.val = generatingLocus ...`.
   PASS. Both sides are scheme opens. The quantifier is after the single f,
   independently over every d>0 and every s, as required.
8. Each chart's induced global-sections map sends ξ/s^n to s^{-n}ξ:
   `∀ n : ℕ, ∀ ξ : sectionRingGrade L (n • d), ...`. PASS.
   I read `Away.mk`, `Away.mk_surjective`, `Proj.awayToSection`,
   `basicOpenIsoAway` and `basicOpenIsoSpec`. Away.mk is literally ξ/s^n;
   positive d makes awayToSection the canonical chart-section isomorphism.
   `f.app` is the actual induced ring homomorphism to the inverse-image open.
   The equality from clause 7 identifies this open with X_s. The scalar image
   times the restricted section `(s.val ^ n) (n • d)` equals the restricted
   numerator `ξ.val (n • d)`. This is equivalent to division because s^n freely
   generates the indicated tensor power on X_s. Away.mk_surjective ensures the
   formula covers every localization element, including nilpotent denominators.

Edge cases: empty X gives a vacuous cover and an allowed zero ring/empty Proj;
zero s is included and both opens are empty; n=0 includes every degree-zero
numerator and denominator 1; d=0 is excluded exactly where the node excludes it.
An empty covering family can cover only empty X. No nonzero object, domain,
reducedness, characteristic, or cardinality assumption is added. The module
universe follows X.Modules at arbitrary v, and every universe/variable is bound.

Independent H4/H12 searches used different conceptual wording:

- LeanFinder through msearch: `graded algebra of all tensor-power sections line
  bundle map homogeneous spectrum` returned chart-localization APIs and
  `Proj.fromOfGlobalSections_resLE`, not this theorem or a sheaf section ring.
- LeanFinder: `open subset where a line bundle section is a basis` returned
  ringed-space scalar basic opens and an unrelated vector-bundle localFrame.
- Loogle: `HomogeneousLocalization.Away.mk` returned seven localization
  constructor/map lemmas; I checked the mk and mk_surjective signatures directly.
- Direct rg in Mathlib AlgebraicGeometry, WeilConjectures, and lean/Sheaf for
  `Γ_*`, `GammaStar`, `sectionRing`, `SectionRing`, and `section ring` found
  ordinary section-ring mentions but no graded tensor-power section ring.
  I opened fromOfGlobalSections: it requires a ring map to ordinary functions,
  so it does not state the theorem for arbitrary invertible L.
- Direct rg of definition nodes for `nonvanishing`, `generatingLocus`, and
  `SectionRing` found no existing node defining either new notion. The ample
  definition mentions nonvanishing opens but does not define this notion.
  The first worker's LeanSearch attempts were unavailable, which is recorded
  as unavailable, not as successful evidence of absence.

New-node review: def-sc-invertible-section-ring agrees with the explicit graded
ring of modules.tex definition-gamma-star and the cited uses in 01PZ/01N8;
its node dependencies, construction module, law declarations, and record fields
match. def-sc-section-generating-locus correctly records the existing source
notion with no duplicate module. Its general free-generator description matches
IsFreeGenerator/GeneratesAt exactly, and its invertible specialization matches
01CY. Both new nodes are cited by the item, have the required definition-node
fields, and do not introduce private replacements of dependencies.

H5/H6/H8/H9: no hollow data, no new theorem proved, all eleven theorem proofs
are sorry, docstrings carry source places and blueprint ids, and the item's
four proof steps correspond to its node. All imports serve the actual statement
or its construction. No declaration-name or namespace mismatch was found.
The two modules compiled together in dependency order on the server, cleanly
in 2.7 seconds with no warnings. The main signature record is now verbatim.
