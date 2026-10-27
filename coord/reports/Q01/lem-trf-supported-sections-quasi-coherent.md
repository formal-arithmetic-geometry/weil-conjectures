## Worker report

Item: `lem-trf-supported-sections-quasi-coherent`. The module
`Sheaf.AlgebraicGeometry.SupportedSectionsQuasiCoherent` states
`AlgebraicGeometry.Scheme.Modules.exists_supportedSections_isQuasicoherent`.
It contains one theorem with proof `sorry`, no definitions, and no other declarations.
The node changes only in `lean`.

Source read: `literature/stacks-project/properties.tex`, lines 3835--3891,
Tag 07ZP, `lemma-sections-supported-on-closed-subset`, assertions (1)--(3)
and its proof. Its hypotheses and assertions agree with the node. The docstring
retains all five steps of the accepted DAG proof, including the finite-generator
power argument and both hypotheses of the principal-open criterion.

Hypotheses and clauses, individually:

- A scheme X: `{X : Scheme.{u}}`, with explicitly bound universe u.
- A closed subset Z: `(Z : Closeds X)`. Its open complement is the actual open
  `⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩`.
- A quasi-coherent O_X-module: `(F : X.Modules) [F.IsQuasicoherent]`.
  This is Mathlib's exact quasi-coherence predicate, exposed by the recorded
  `pqf-def-coherent` module; finite type and coherence are not assumed.
- Retrocompact complement: `hretro` quantifies over every open U and every
  `IsAffineOpen U` and requires `IsCompact ((U : Set X) ∩ (Z : Set X)ᶜ)`.
  There is no assumption that X is quasi-compact or quasi-separated.
- The submodule sheaf K with K(W) the sections restricting to zero off Z:
  the conclusion exhibits `(K : X.Modules) (ι : K ⟶ F)` and, for EVERY open W,
  states both `Function.Injective (ι.app W)` and the equality of its range
  with `{s : Γ(F, W) | F.presheaf.map (...) s = 0}`. The restriction arrow is
  induced by `W ⊓ complement ≤ W`, so its target is exactly W minus Z.
  Since ι is a morphism of O_X-modules, the images are submodules with compatible
  restriction maps. This describes the prescribed subsheaf itself via its
  inclusion, without choosing arbitrary auxiliary data or defining a second
  supported-sheaf notion. The existential is the construction assertion of
  the node's first proof step, not an extra hypothesis on an unspecified K.
- K is quasi-coherent: `K.IsQuasicoherent`, after the sectionwise characterization.
- For EVERY affine open U = Spec A: the final universal quantifier is
  `∀ (U : X.Opens) (hU : IsAffineOpen U)`. Here A is the canonical ring
  `Γ(X, U)`, and `hU.isoSpec` identifies U with its spectrum.
- Existence of a finitely generated defining ideal: `∃ J : Ideal Γ(X, U), J.FG ∧ ...`.
  The remaining predicate is `∀ x : U, x.1 ∈ Z ↔ J ≤ (hU.isoSpec.hom x).asIdeal`.
  Under the canonical affine isomorphism this says precisely Z intersect U = V(J),
  with V(J) the prime ideals containing J. No different zero-locus convention is used.
- For EVERY such finitely generated J, not only one selected witness: a separate
  `∀ J, J.FG → (∀ x, ...) → ...` quantifier gives the description.
- K(U) equals the ideal-power torsion subset: for every `m : Γ(F, U)`,
  `m ∈ Set.range (ι.app U) ↔ ∃ n : ℕ, ∀ a : Γ(X, U), a ∈ J ^ n → a • m = 0`.
  Membership in the range identifies K(U) with its actual submodule of F(U).
  A single n kills m by EVERY element of J^n. Naturals include n = 0.

Statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; the structure
  and docstrings were read in `Scheme.lean`, lines 36--76.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, publicly
  imported exactly as recorded. Read the complete module and Mathlib
  `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`, lines 249--260.
  The relevant recorded declaration is `SheafOfModules.IsQuasicoherent`.
  `Scheme.Modules.IsQuasiCoherentFiniteType` is the conjunction for another clause
  and is deliberately not used as the quasi-coherence hypothesis.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, read at lines 469--480. The affine identification
  `AlgebraicGeometry.IsAffineOpen.isoSpec` and its signature/docstring were read
  in `Mathlib.AlgebraicGeometry.AffineScheme`, lines 379--405.

Proof dependencies are available through ordinary imports:
`Mathlib.RingTheory.Spectrum.Prime.Topology` for
`PrimeSpectrum.isTopologicalBasis_basic_opens` (and the recorded localization
embedding and range declarations);
`WeilConjectures.AlgebraicGeometry.Modules.QcqsSections` for
`exists_pow_smul_eq_zero_of_isCompact` and
`exists_map_eq_pow_smul_of_isCompact_of_isQuasiSeparated` (signatures and
source docstrings read at lines 63--96);
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` for
`isQuasicoherent_of_forall_isAffineOpen` (full signature and docstring read).
Affine compactness is `Scheme.compactSpace_of_isAffine` in `AffineScheme`,
and quasi-separatedness is `quasiSeparatedSpace_of_isAffine` in
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, exposed by the proof imports;
both recorded instance signatures were read. No missing-interface repair is needed.

Edge cases checked before writing:

- Z = X: restrictions land on the empty open, K = F; J = 0 is finitely generated,
  and exponent 1 annihilates every m. The empty basic-open cover in the proof works.
- Z empty: K = 0; J = the unit ideal defines the empty subset, and its powers kill
  precisely zero. The quantifier over all other finitely generated defining ideals
  is retained.
- Empty X or empty affine U: all pointwise defining-ideal predicates are vacuous;
  sheaf sections over the empty open are zero, and the zero ideal works.
- n = 0: J^0 is the unit ideal, so the all-elements condition forces m = 0.
- Zero module: both section descriptions give just zero. No ring characteristic,
  nontriviality, separatedness, Noetherian, or finite-type assumptions were added.

Searches actually run through the prescribed `msearch.py` for this item:

1. LeanFinder: "For a quasi coherent sheaf on a scheme, sections supported on a
   closed subset with retrocompact complement form a quasi coherent subsheaf and
   affine sections are killed by ideal powers". Eight hits: structure-sheaf
   qcqs section lemmas and ideal-sheaf constructors; no exact module-sheaf theorem.
2. Loogle: `SheafOfModules.IsQuasicoherent, AlgebraicGeometry.Scheme.Modules`.
   Six hits, including the affine tilde comparison and quasi-coherence under
   restriction; no supported-sections theorem.
3. LeanSearch: "subsheaf of sections supported on a closed subset of a scheme".
   Eight hits: ideal-sheaf support/vanishing-ideal lemmas, `Scheme.zeroLocus_isClosed`
   and `Finsupp.supported`; no exact statement.
4. Grep: `sectionsSupported|sections_supported|supportedOn|supportedIn`, restricted
   to Mathlib `AlgebraicGeometry`. Zero hits.

Additional direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` used
` supportedSections|sectionsSupported|supportedOn|supported.*[Kk]ernel|supported.*[Ss]ubsheaf|SupportedSections`
(without the initial space). Relevant neighboring hits were etale/pro-etale
supported-kernel constructions, the abelian-sheaf `supportedIn` in
`WeilConjectures/Topology/Sheaves/GrothendieckVanishing.lean` (definition read at
lines 95--100; it is for constant abelian coefficients, not O_X-modules), and
`subcanonicalSupportedSections`, which is only a submodule of GLOBAL sections.
None states this lemma. Focused searches of the upstream modules directory found
no O_X-module supported-subsheaf declaration. `grep -rn` for the item id in
`lean/WeilConjectures` found nothing. Searches of `dag/lean_names_upstream.json`
for supported sections and the chosen declaration name found no match.
The chosen full name was also searched in Mathlib, both source trees, and the
upstream name map: no collision.

Validation: `scompile.py Q01 lem-trf-supported-sections-quasi-coherent` compiled
both sandbox and library forms cleanly (8.1 s and 8.3 s). All variables and the
universe are explicitly bound, `autoImplicit` is false, and every line is at
most 100 characters. No statement fault or disputed claim was found.

## Second reading by Q01

This is the dispatcher's requested author self-check; independent maintainer
review follows delivery. I reopened the node and the final Lean statement and
compared them with Stacks 07ZP (1)--(3). Closed Z and the affine-intersection
compactness condition render exactly the hypotheses. The section image equality
uses W intersect the OPEN complement of Z, not W intersect Z. Injectivity makes
this the submodule subsheaf specified by the node; K is concluded quasi-coherent.
The affine-ring identification uses `hU.isoSpec` into Spec of Γ(X,U), so prime
containment is in the correct ring. The existential finitely generated ideal
and the second, universal quantifier over every such ideal are both present.
The final quantifier requires one exponent valid for every element of J^n;
it does not swap these quantifiers or exclude exponent zero. The statement has
no additional finiteness or separation condition. The first compiler run was
clean; this second reading found no mismatch and made no change to the signature.
