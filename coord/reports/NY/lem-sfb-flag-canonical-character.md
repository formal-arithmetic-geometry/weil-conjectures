## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FlagCanonicalCharacter` states
`AlgebraicGeometry.flag_canonical_character`. It uses the semisimple simply connected
hypotheses from `hS` and `hsc`, and the fixed split maximal torus and Borel pair in
`hTB`. The recorded positive-root list is `Φ`; `Φ.length` renders
`N = |Φ⁺|`. The action hypothesis `ha` identifies the Borel action with conjugation,
and `hroots` identifies the list with exactly the nonzero tangent weight spaces.
The character hypotheses `hρ`, `hρB`, and `hρU` render that `ρ` is the actual half-sum
character, that `ρB` extends it, and that it is trivial on every unipotent normal
subgroup. The quotient hypotheses `hQ`, `hQft`, `hQqc`, `hπf`, `hπs`, `hπi`, and `hπt`
render the proper flag quotient and its right B-torsor.

The conclusion `SmoothOfRelativeDimension Φ.length Q.hom` renders smoothness and pure
dimension `N`. The module
`Scheme.Modules.exteriorSheaf Q.hom.relativeDifferentials Φ.length` is the glued
exterior power of the actual relative Kähler differential sheaf, hence renders
`ω_Q = ⋀^N Ω¹_{Q/F}`, and `IsInvertible` renders that it is a canonical line sheaf.
The existential `χ` with `χ.hom.hom = ρB.hom.hom ^ 2` renders the character
`2\widetilde ρ`; the `Presentation` and its isomorphism render
`ω_Q ≃ L_{2\widetilde ρ} = M_{-2ρ}` under the quotient action convention from
`AssociatedCharacterLineBundle`. The final implication handles `N = 0`: the quotient
is the base point and both exterior power and associated line sheaves are isomorphic
to the structure sheaf. No characteristic restriction is added.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.RhoSectionModules`,
  `AlgebraicGeometry.IsRhoBorelPair` and `AlgebraicGeometry.exists_rho_section_modules`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`,
  `AlgebraicGeometry.reductive_borel_pair_structure` and
  `AlgebraicGeometry.semisimpleGroupScheme_isReductive`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections`,
  `AlgebraicGeometry.RankOneRoots.reductive_rankOne_reflections`.
- `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousLineBundleSections`,
  `AlgebraicGeometry.exists_homogeneousLineBundle_sections`.
- `Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle`,
  `AlgebraicGeometry.AssociatedCharacterLineBundle.Presentation`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`,
  `AlgebraicGeometry.Scheme.Modules.exteriorSheaf` and
  `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_zero_iso`.
- Mathlib `Field`, `IsAlgClosed`, `GrpObj`, `SmoothOfRelativeDimension`,
  `KaehlerDifferential`, and `AlgebraicGeometry.Etale` interfaces as recorded by the
  dependency nodes.

Edge cases checked: `Φ = []` gives `Φ.length = 0`, the empty wedge, and the empty
character product; the theorem explicitly states both resulting line sheaves are
trivial. The character equation is multiplicative (`ρ² = ∏ Φ`), so characteristic two
is included. The list is only required to be `Nodup`, and no nonempty root-system or
positive-rank assumption is imposed.

Searches made: `msearch.py ... leanfinder` for the canonical line bundle of a flag
variety (returned only Lie-module/root-system determinant results, no flag-bundle
statement); `msearch.py ... leansearch` for the canonical sheaf as determinant of
relative differentials (returned differential presheaf and Kähler declarations, no
flag statement); `msearch.py ... loogle` for `Scheme.Hom.relativeDifferentials` and
`Scheme.Modules.exteriorPower` (unknown identifier/no match); grep of Mathlib,
`WeilConjectures`, and `Sheaf` for `canonical.*[Ff]lag|flag.*canonical|twice.*rho`
(no matching declaration). The needed differential and exterior-power notions were
therefore reused from their recorded declarations.

Source verification: read the author-hosted Brion--Kumar PDF, Section 2.1,
printed pp.63--64, equation (8), including the convention L(lambda) = G ×^B k_(-lambda).
The source formula omega = L(-2 rho) is therefore exactly our L_(2 rhoB) = M_(-2 rho).
The source was opened at https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf.

Proof-only nodes homogeneous-cotangent-associated-bundle, regular-cocharacter-borel-description,
and unipotent-to-multiplicative-trivial have no recorded Lean declaration at the read base;
their future imports remain for the maintainer. No proof is supplied here.

Validation: scompile.py passed both sandbox and library module compilations (48.2 s and 8.9 s),
with no compiler errors or warnings. The only postponed proof is the named theorem.

Independent review is performed by the maintainer under the current dispatcher protocol;
no independent worker reading is claimed in this report.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
