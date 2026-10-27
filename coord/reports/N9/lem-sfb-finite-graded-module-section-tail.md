## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteGradedModuleSectionTail` states
`AlgebraicGeometry.Proj.finite_graded_module_section_tail`, with exactly one
postponed theorem and no new definitions. Its proof is `sorry`. The source is
Stacks Project, coherent.tex, Tag 0AG7, lemma-recover-tail-graded-module
(lines 3862–3929 in the read clone), together with constructions.tex Tag 01MT
for the shift/tensor identification. The complete nine-step proof of the
reviewed node is retained in the theorem docstring.

The previous dispatch result concerned the reviewed stage-1 split. That split
was merged from Q10 at 04:50 UTC; it has no Lean record. This delivery is stage 2:
it preserves that statement, proof, proof dependencies and all review fields.
Only `lean` and additions of already recorded statement dependencies change.

Hypotheses and clauses, matched to Lean:

- The nonnegatively graded commutative ring is `{S : Type u} [CommRing S]`,
  `𝒜 : ℕ → AddSubgroup S`, and `[GradedRing 𝒜]`. This is Mathlib's internal
  direct-sum ring grading, with its existing degree-zero subring and algebra.
- Noetherianity of S_0 is `[IsNoetherianRing (𝒜 0)]`; it is not replaced by
  the stronger assumption that S_0 is a field or that S itself is given Noetherian.
- Finite generation as an S_0-algebra by degree-one elements is `hgen`:
  there exist `r : ℕ` and `f : Fin r → S`, all `f i ∈ 𝒜 1`, whose
  `Algebra.adjoin (𝒜 0) (Set.range f)` is top. The empty family is allowed.
- The finite integer-graded S-module is `{M : Type v} [AddCommGroup M]`
  `[Module S M] [Module.Finite S M]`, together with `𝓜 : ℤ → AddSubgroup M`
  and `h𝓜 : DirectSum.IsInternal 𝓜`. Its multiplication law is precisely
  `hsmul`, landing in `𝓜 ((a : ℤ) + b)`.
- X is the existing Mathlib `Proj 𝒜`; all chart restrictions are evaluated
  on the existing `basicOpen 𝒜 f`. There is no separate scheme parameter.
- The shift M(n)_d = M_(n+d) occurs literally in
  `fun k : ℕ ↦ (𝓜 (n + k) : Set M)` inside `degreeZeroFractions`.
  The index k is the degree of a homogeneous denominator, not its exponent:
  for a denominator f^m its degree is m*deg(f). Thus its numerator belongs
  to M_(n+m*deg(f)), exactly as required.
- The associated sheaf of M(n) is `F`, with chart maps `alpha` that are
  injective and have range exactly those shifted degree-zero fractions.
  Their explicit scalar law identifies the module structure over S_(f)
  via `awayToSection`. The next conjunct is the canonical restriction
  formula y/f^m ↦ a^m*y/g^(e*m) whenever g^e = a*f. These are precisely
  the section, scalar and restriction data supplied by the recorded
  `gradedModuleSheaf_exists`, followed by the submodule inclusions.
- H^0(X,F) is its group of global sections `F.val.obj (op ⊤)`. No positive
  cohomology is involved; this is the degree-zero/global-sections reading
  of the recorded cohomology node, rather than a different cohomology theory.
- `eta : 𝒜 0 →+* (Proj 𝒜).presheaf.obj (op ⊤)` is fixed by its chart
  restrictions `awayToSection 𝒜 f (fromZeroRingHom 𝒜 _ r)`, i.e. r/1.
  Thus the target has the canonical S_0-action, including when X is empty.
- `gamma : 𝓜 n →+ F.val.obj (op ⊤)` is the canonical map: on every positive
  homogeneous chart its image under alpha is exactly `mk (x : M) 1`.
  Sheaf separatedness and injectivity of alpha determine this map uniquely.
  This is not an unconstrained map or an arbitrary isomorphism.
- The displayed law `gamma y = eta r • gamma x` whenever the underlying
  representatives satisfy `y = r • x` states S_0-linearity. Existence of
  such y is supplied by hsmul with a=0; its value is unique by subtype
  extensionality. This formulation avoids a second scalar instance or
  a proof-dependent transport between 0+n and n.
- `Function.Bijective gamma`, together with that additive and scalar law,
  says the specified S_0-linear map is an isomorphism. The bound is
  `∃ n0 : ℤ, 0 ≤ n0 ∧ ∀ n : ℤ, n0 ≤ n → ...`.
- The associated sheaf, its chart identifications and canonical maps are
  existentially packaged in the conclusion, since the existing dependency
  supplies the associated sheaf existentially, uniquely up to the chart-compatible
  isomorphism. This does not weaken recovery to an arbitrary choice: every
  other associated sheaf is uniquely isomorphic compatibly with these alpha
  maps, and this isomorphism carries gamma to its own x/1 section map.
  Consequently bijectivity here is equivalent to bijectivity for the
  associated sheaf named in the node. There is no assumption that such a
  map is bijective and no choice of data from a sorry proof in a definition.
- No nonempty-Proj or irrelevant-torsion-free hypothesis is present. The
  module and ring have independent explicitly bound universes u and v;
  F has coefficient universe max u v. No universe equality is imposed.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` (publicly available
  through the associated-sheaf module): `AlgebraicGeometry.Proj`,
  `AlgebraicGeometry.Proj.basicOpen`, `awayToSection`, and
  `HomogeneousLocalization.fromZeroRingHom`. The recorded `projIsoSpec`
  identifies these standard opens with their homogeneous localizations.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`:
  `AlgebraicGeometry.Proj.twist`, the recorded shift/twist convention.
  The general module sheaf clause of its node explicitly refers consumers
  to `gradedModuleSheaf_exists`, which is used directly here.
- `WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists`:
  `AlgebraicGeometry.Proj.gradedModuleSheaf_exists`. Its full chart, scalar,
  restriction, uniqueness and degree-zero section interface was read. This
  existing recorded node is added to stmt_deps, rather than repairing or
  privately copying the general associated-sheaf notion.
- `WeilConjectures.Algebra.Module.DegreeZeroFractions`:
  `LocalizedModule.degreeZeroFractions`, used for the exact chart ranges;
  its already recorded node is added to stmt_deps as well.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, recording
  `RingedSpace.moduleCohomology` as right derived global sections.

All recorded proof-dependency modules are imported, including the Mathlib leaves:
`Mathlib.RingTheory.FiniteType`, `Mathlib.Algebra.Module.FinitePresentation`,
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`,
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`,
`WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial`, and
`Sheaf.Algebra.Module.GradedLocalizationExact`. The three proof dependencies
`lem-sfb-standard-proj-coherent-section-finiteness`,
`lem-sfb-standard-proj-twist-tensor`, and
`lem-sfb-proj-section-module-reconstruction` have no recorded Lean module at
this reading, so they have no import to add. They remain the named stage-3
proof plan in the docstring; none is needed to type the statement.

Edge cases checked before writing:

- M=0: every shifted localization and global-section module is zero; gamma
  is bijective in every degree.
- No degree-one generators, or a nilpotent irrelevant ideal: Proj can be
  empty. The fraction chart modules vanish; a finite graded module is zero
  in high degrees. The zero global-section group and canonical scalar map
  are permitted, so the conclusion still holds.
- A finite module killed by a power of the irrelevant ideal: its associated
  sheaf is zero, but only its sufficiently high pieces must be zero. Nothing
  in the signature excludes these modules.
- Negative homogeneous generator degrees and arbitrary integer shifts:
  `𝓜 : ℤ → AddSubgroup M` and n in ℤ retain these cases. The final bound
  is nonnegative but the input module need not have vanishing negative pieces.
- S=k[t] and a shifted free module: the high-degree component and the
  sections on Proj(k[t]) agree, with exactly the n+d shift sign.
- Nilpotent f and empty charts: ordinary `LocalizedModule.Away f M` is the
  zero module, with the same fraction relation. No chart nonemptiness or
  regularity of f is assumed.

Searches made on this attempt (in addition to reading the node's searches):

- msearch.py LeanFinder: “Finite graded module over a standard graded
  Noetherian ring recovered by global sections of shifted associated sheaves
  in sufficiently large degrees”. Eight hits: finite type of Proj and its
  homogeneous localizations, structure sheaf and Noetherian grading facts;
  none states recovery of a general finite graded module.
- msearch.py Loogle: `AlgebraicGeometry.Proj, Module.Finite`: zero hits.
- msearch.py grep, AlgebraicGeometry: `recover.*graded|graded.*recover|section.*[Tt]ail`:
  zero hits.
- msearch.py LeanSearch: “For a finite graded module over a degree-one
  generated Noetherian graded ring the canonical map to global sections on
  Proj is bijective in all sufficiently high degrees”: eight hits, all Proj
  structure sheaf, chart, or toSpecZero constructions, not this theorem.
- rg in the read clone's WeilConjectures and Sheaf sources for
  `recover.*graded|graded.*recover|section.*[Tt]ail|gradedModuleSheaf|finite_graded`
  located the associated-sheaf interface, P^1-specific graded representations
  and unrelated tail lemmas; no declaration states this general recovery.
  `grep -rn lem-sfb-finite-graded-module-section-tail lean/WeilConjectures`
  found no declaration for this item. Source declarations were read directly.

No statement correction, dependency repair or new definition node was needed.
There is no STATEMENT-DISPUTED finding. The initial scompile.py check compiled
both the sandbox and named library module cleanly (10.2 s and 8.0 s), with no
warnings. Every subsequent compile and preflight is through the prescribed
wrappers; no live sources or compiled library artifacts are edited directly.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
