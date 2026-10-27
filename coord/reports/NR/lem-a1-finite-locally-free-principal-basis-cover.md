## Worker report

Module: `Sheaf.AlgebraicGeometry.FiniteLocallyFreePrincipalBasisCover`.
The only postponed proof is `AlgebraicGeometry.finiteLocallyFree_principalBasisCover`.
Two transparent auxiliary constructions bundle existing objects; neither contains a sorry:
`affineAlgebraStructurePushforward` is precisely the pushforward of the unit structure module,
and `affineAlgebraLocalizedModule` bundles `LocalizedModule.Away f B` with Mathlib's existing
`LocalizedModule.moduleOfIsLocalization` action as a `ModuleCat (Localization.Away f)`.
There are no new independent notions, dependency repairs, or statement corrections.

Hypotheses and conclusions, clause by clause:

- Commutative rings A and B are `(A B : Type u) [CommRing A] [CommRing B]`.
  The given unital homomorphism is `[Algebra A B]`, with phi = `algebraMap A B`.
  Every unital homomorphism supplies exactly this structure by `RingHom.toAlgebra`;
  no restriction such as injectivity, nontriviality, or finite type is imposed here.
  The intended p is explicitly `Spec.map (CommRingCat.ofHom (algebraMap A B))`.
  The node leaves its equality with Spec phi implicit; its proof and source use this p.
- The nonnegative degree is `(r : ℕ)` and the hypothesis is the recorded
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree` class on precisely that spectrum morphism.
  This includes finiteness, flatness, local finite presentation, and fibre degree r.
- E is `affineAlgebraStructurePushforward A B`, definitionally the actual
  `Scheme.Modules.pushforward p` applied to `SheafOfModules.unit` on Spec B.
- Quasi-coherence is the first conjunct, `E.IsQuasicoherent`.
  Constant local rank r is the second, `SheafOfModules.IsFiniteLocallyFreeOfRank E r`.
- The finite family is `∃ (m : ℕ) (f : Fin m → A)`; the unit ideal is exactly
  `Ideal.span (Set.range f) = ⊤`. This also says that the D(f i) cover the spectrum,
  by the recorded `PrimeSpectrum.iSup_basicOpen_eq_top_iff`.
- The chosen fixed-rank bases are `b : Module.Basis (Fin r) (Localization.Away (f i))
  (affineAlgebraLocalizedModule A B (f i))`. The underlying module is B_f, not
  a module only assumed isomorphic to it. The scalar structure is canonical.
- `eR` is a ring equivalence A_f ≃ O(D(f)). Its equation on every numerator a
  says it extends the actual restriction of the global section of Spec A associated
  with a by `Scheme.ΓSpecIso`. Since it is a ring equivalence out of a localization,
  this fixes the map on every a/f^n, including the displayed inverse-power formula.
- `eM` is an additive equivalence B_f ≃ E(D(f)). Its scalar equation
  `eM (a • z) = eR a • eM z` makes it a compatible module isomorphism over eR.
  Its next equation specifies its value on EVERY fraction t/f^n as eR(f^-1)^n
  times the restriction of the global section t. The target is the actual E(D(f)),
  whose underlying additive group is O_SpecB(p^-1 D(f)); the explicit `@id` only
  exposes that definitional equality to elaboration. No arbitrary map is substituted.
- `eB` is the ring equivalence B_f ≃ B[1/phi(f)]. The equation on every fraction
  sends t/f^n to t/phi(f)^n. The existing localized-module ring structure is used.
  This formula also determines the induced algebra structure and its compatibility.
- `θ` is an isomorphism from the free sheaf indexed by `ULift (Fin r)` to E over
  D(f). `E.over D(f)` is the existing restriction to the over-site, equivalent to
  the usual module on the open subscheme. The last equation sends the j-th coordinate
  section `ιFree (ULift.up j)` evaluated at 1 to `eM (b j)`. A sheaf morphism from a
  finite free sheaf is determined by these sections. Thus on every smaller open it
  is exactly the linear combination of their restrictions, as the node requires;
  this is stronger information than an unspecified trivialization.
- For A nonzero, `Nontrivial A → ∀ i, (D(f i) : Set (PrimeSpectrum A)).Nonempty`.
  For A zero, `Subsingleton A → Subsingleton B` explicitly records B zero, and
  `Subsingleton A → m = 0` chooses the permitted empty family. Empty span is top
  in the zero ring. Neither Nontrivial nor Subsingleton is a hypothesis of the theorem.
- No Noetherian, global freeness, or positive-rank assumption occurs.

Recorded dependency declarations read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`,
  and `Scheme.ΓSpecIso` for the canonical global sections.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `Scheme.Hom.IsFiniteLocallyFree` and `Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
- `def-amb-finite-locally-free-module`:
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  `SheafOfModules.IsFiniteLocallyFreeOfRank`. Also read the scheme interface
  `Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`,
  with the actual basis data `Module.Basis`; the statement needs the fixed index Fin r.
- `def-weil-ring-localization-away`: `Localization.Away` (the recorded monoid-localization
  abbreviation), its commutative ring structure, `IsLocalization.Away.invSelf`,
  and `IsLocalization.mk'`, provided by `Mathlib.RingTheory.Localization.Away.Basic`.
- `def-weil-pbc-module-localization-away`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule.Away`,
  `LocalizedModule.mk`, and its canonical localized scalar action. Imported through Away.

Proof-dependency modules are imported without `public`: the recorded
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf` with
`finiteLocallyFree_structureSheaf_properties`; the recorded module localization lemmas
`exists_map_eq_pow_smul_of_isAffineOpen` and `exists_pow_smul_eq_zero_of_isAffineOpen`
in `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`; Mathlib's AffineScheme
and ResidueField for `IsAffineOpen.isLocalization_basicOpen`, `IsAffineOpen.basicOpen`,
`Scheme.evaluation_eq_zero_iff_notMem_basicOpen`, `IsAffineOpen.fromSpec_preimage_basicOpen`,
and `IsAffineOpen.fromSpec_primeIdealOf`. The recorded principal-open basis, localization
embedding/range, compactness and unit-ideal results of `PrimeSpectrum` are available
through these imports. No proof-dependency import was omitted for a cycle.

Source checked locally: morphisms.tex, lemma-finite-flat (02KB) and
lemma-finite-locally-free (04MH); schemes.tex, lemma-quasi-coherent-affine (01IA).
The docstring records all four node proof steps and their dependency identifiers.

Edge cases checked mathematically before writing: the zero base ring forces B zero
by unitality and allows m=0 for every r; rank zero over a nonzero base has B=0 and
empty bases, with nonempty principal cover possible (e.g. D(1)); disconnected spectra
and nilpotent elements cause no issue, and principal opens that are empty are excluded
only by the optional nonzero-base conclusion. Universes are explicitly declared;
ULift gives the finite index the structure sheaf's universe without changing its size.
No free-standing auto-bound variables, file-local notation, or local instances occur.

Searches actually run with `batch2/msearch.py NR <item>`:

- leanfinder: "A finite locally free affine algebra of degree r admits a finite principal
  open cover with bases and canonical section localization isomorphisms". Eight hits:
  affineBasisCoverOfAffine, affineBasisCover, affineBasisCoverRing, Proj.affineOpenCover,
  and four affineOpenCoverOfSpanRangeEqTop declarations. These construct affine covers
  or use supplied unit-ideal data, but do not extract fixed-rank bases and identify sections.
- loogle: `Module.FinitePresentation, Module.Free`. Five hits, including
  `Module.FinitePresentation.exists_free_localizedModule_powers`. Read its signature
  and the preceding exists_basis lemma: they spread an already supplied free
  localization; they do not give this entire scheme-degree and section statement.
- grep: `exists_basis_localizedModule_powers|isLocalization_basicOpen`. Twenty-five hits;
  the localization-of-sections results in AffineScheme were read. They supply the
  ring part and not the requested module bases and compatible sheaf trivializations.
- leansearch: "A finite locally free algebra of fixed rank has a finite principal open
  basis cover and canonical localization of its sections". Eight hits:
  Γ_restrict_isLocalization, toΓSpecCApp, StructureSheaf.localization_toBasicOpen,
  Algebra.QuasiFinite.instLocalization, IsAffineOpen.isLocalization_of_eq_basicOpen,
  affineBasisCoverOfAffine, StructureSheaf.IsLocalization.to_basicOpen and
  StructureSheaf.toBasicOpen. These provide parts of the section-localization construction;
  none states the complete conclusion under the fixed-degree hypothesis.
- rg of both `lean/WeilConjectures` and `lean/Sheaf`: principal/basis/localization patterns
  and the exact item identifier. The norm characteristic polynomial and principal-open
  finite-projective tilde modules are related but not this statement. Exact searches for
  all three new declaration names found no collisions in Mathlib or the project.

Validation: prescribed scompile.py passed both sandbox and named-library compilation
without errors or warnings (5.7 s and 4.8 s). Delivery dry run follows.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
