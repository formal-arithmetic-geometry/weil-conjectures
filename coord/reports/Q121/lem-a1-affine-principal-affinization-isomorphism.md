## Worker report

The module `Sheaf.AlgebraicGeometry.AffinePrincipalAffinizationIsomorphism` states
`AlgebraicGeometry.affine_principal_affinization_isomorphism`. Its only proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The node is unchanged outside `lean`.

Source read: `literature/stacks-project/properties.tex`, lemma-invert-f-affine
(Tag 01P8), lines 2433 onward, including its proof using lemma-invert-f-sections.
The statement includes the explicit section-ring formula required by the DAG node.
The declaration docstring retains all three proof steps and their cited node ids,
including the Laurent-variable argument that never cancels the possibly nilpotent f.

Hypotheses and clauses, in order:

- A scheme X is `(X : Scheme.{u})`, with `universe u` explicitly declared.
- Quasi-compactness is `[CompactSpace X]`, exactly the recorded dependency notion,
  with no Hausdorff hypothesis.
- Quasi-separatedness is `[QuasiSeparatedSpace X]`. Mathlib's
  `quasiSeparatedSpace_iff_forall_affineOpens` identifies this with quasi-compact
  intersections of any two affine opens, exactly the explanatory clause of the node.
- C is the existing ring `Γ(X, ⊤)` and its element is `(f : Γ(X, ⊤))`.
- X_f is the existing open `X.basicOpen f`, whose unit-germ meaning is
  `Scheme.mem_basicOpen_top`. Its affineness is `(hf : IsAffineOpen (X.basicOpen f))`.
- The canonical j is `X.toSpecΓ`, the unit of `ΓSpec.adjunction`, corresponding to
  the identity on C. D(f) is `PrimeSpectrum.basicOpen f` in `Spec Γ(X, ⊤)`.
- The first conjunct is literally
  `X.toSpecΓ ⁻¹ᵁ (PrimeSpectrum.basicOpen f) = X.basicOpen f`.
- The second conjunct is `IsIso` of
  `X.toSpecΓ.resLE (PrimeSpectrum.basicOpen f) (X.basicOpen f)
  (X.toSpecΓ_preimage_basicOpen f).ge`.
  Thus the morphism is the restriction of the specified canonical j, with its
  preimage equality supplying the restriction inclusion.
- The third conjunct gives a ring equivalence
  `e : Localization.Away f ≃+* Γ((X.basicOpen f).toScheme, ⊤)` and fixes its
  underlying homomorphism by `e.toRingHom = (X.awayToBasicOpen f).hom`.
  This existing canonical map is defined in upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme` as global sections of
  `X.toSpecAway f`, preceded by `(Scheme.ΓSpecIso _).inv`.
  `toSpecAway` is exactly the above restricted j composed with
  `(basicOpenIsoSpecAway f).hom : D(f) ⟶ Spec (Localization.Away f)`.
  Consequently the map is the section homomorphism of j_f under the specified
  canonical localization identification, not an arbitrary ring isomorphism.
  Sections of the open subscheme and sections of O_X on that open identify via
  `(X.basicOpen f).topIso`, already in Mathlib.
- Finally `∀ (a : Γ(X, ⊤)) (n : ℕ)` quantifies over every numerator and exponent.
  `IsLocalization.mk' (Localization.Away f) a (Submonoid.pow f n)` is a/f^n.
  The equation sends this to `(X.basicOpen f).ι.appTop a` times
  `Ring.inverse ((X.basicOpen f).ι.appTop f) ^ n`.
  The inclusion's `appTop` is restriction. Its value on f is a unit by the existing
  `Scheme.isUnit_ι_appTop_basicOpen`, so `Ring.inverse` is its actual inverse.
  This is precisely a|X_f/(f|X_f)^n, including exponent zero.

Dependency declarations read and used:

- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`,
  `Mathlib.Topology.Defs.Filter` (available through the public imports).
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `lem-weil-pbc-morphism-into-affine-scheme`: `AlgebraicGeometry.ΓSpec.adjunction`,
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`; its unit is `Scheme.toSpecΓ`.
  The exact preimage equality is `Scheme.toSpecΓ_preimage_basicOpen` there.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-ring-localization-away`: `Localization.Away`,
  `Mathlib.GroupTheory.MonoidLocalization.Away`; fractions use the existing
  ring-localization `IsLocalization.mk'` and `Submonoid.pow`.
- The proof imports `Mathlib.AlgebraicGeometry.ResidueField` and
  `Mathlib.AlgebraicGeometry.Morphisms.IsIso` expose the affine-open localization
  and affine-global-sections criteria recorded in the two Mathlib proof leaves.
- The recorded module
  `WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization` and declaration
  `AlgebraicGeometry.Scheme.Modules.exists_sectionFraction_nonvanishing_equiv`
  are imported for proof step 2.
- The other recorded proof modules are imported as ordinary imports:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, declaration
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, and
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`, declaration
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
  For the structure module only quasi-coherence is needed; its existing
  `SheafOfModules.IsQuasicoherent` notion remains unchanged.

Edge cases checked before writing: the empty scheme and zero section ring are
allowed; f = 0 and nilpotent f give empty basic opens and zero localizations;
a unit f gives the whole scheme, affine by hf; n = 0 gives restriction of a.
No nonzero, reducedness, nonempty, domain, or characteristic assumption is added.
The single scheme universe u matches the universes of its section ring and opens,
with no quantification over test objects in a smaller universe.

Searches (all via the prescribed msearch.py Q121 item wrapper unless stated otherwise):

- leanfinder: "For a quasi compact quasi separated scheme the affinization map
  restricts to an isomorphism on an affine principal open and on sections is the
  fraction localization map". Eight hits, including
  `isIso_ΓSpec_adjunction_unit_app_basicOpen`, `basicOpenSectionsToAffine_isIso`,
  `SpecMapRestrictBasicOpenIso`, and `Γ_restrict_isLocalization`.
- loogle: `"toSpecΓ", "basicOpen"`. Two hits:
  `Scheme.toSpecΓ_preimage_basicOpen` and its open-subscheme version.
- grep: `isIso_ΓSpec_adjunction_unit_app_basicOpen|basicOpenSectionsToAffine_isIso|basicOpenIsoSpecAway`
  in AlgebraicGeometry. Seventeen hits, principally the same results and their uses.
- leansearch: "The affinization morphism of a quasi compact quasi separated scheme
  restricts to an isomorphism on an affine principal open and its ring map sends
  fractions to restricted fractions". Eight hits, including the same section-map
  isomorphism, `StructureSheaf.toBasicOpen`, and `basicOpenIsoSpecAway`.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for
  `affinization|isIso_ΓSpec_adjunction_unit_app_basicOpen|basicOpenSectionsToAffine|basicOpenIsoSpecAway|affinePrincipal`;
  found the upstream canonical maps `Scheme.toSpecAway` and
  `Scheme.awayToBasicOpen`, which are reused. Searching the item id in
  `lean/WeilConjectures` gave no match. Searching all three Lean trees for the
  proposed theorem name gave no match.

None of the search hits states the complete item: the qcqs instance establishes
that a section map is an isomorphism, not that the restricted scheme morphism is
an isomorphism together with the fixed localized ring equivalence and fraction
formula. The affine-source comparison alone is not the qcqs result here.
No disputed statement or other node fault was found.

Validation: prescribed scompile.py compiled the sandbox and final library module
successfully (5.3 s and 1.8 s), without errors or warnings.

## Second reading by Q121

I reread the node, the source lemma, and the final signature after compilation.
The dispatcher explicitly forbids starting another agent; this is a separate
self-check, with the maintainer's independent review still to follow.
The scheme, qcqs hypotheses, f, and affine-open hypothesis are all present. The
preimage equality uses the canonical affinization map. The `IsIso` concerns its
actual `resLE`, and the ring equivalence is tied to the existing canonical
`awayToBasicOpen`, whose definition uses exactly that restriction and the canonical
`basicOpenIsoSpecAway`. This tie rules out an unrelated ring equivalence. The
formula quantifies over all a and n and uses the inverse of the restricted unit.
The open-subscheme section ring is identified with O_X(X_f) by the existing topIso.
No mismatch was found and no mathematical statement was changed.
