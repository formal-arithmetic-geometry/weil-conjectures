## Worker report

The delivery states `SheafOfModules.OpenTensorNormalization.open_system_tensor_shift`
in `lean/Sheaf/SixFunctors/OpenSystemTensorShift.lean`. Its only proof is `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The original node changes only in `lean`. No source or shared-repository file was edited.

The theorem uses the existing normalization package rather than a new presentation of
strict systems or an arbitrary comparison. The parameter `a : Assertion o` supplies
exactly the specified delta as `a.gamma`: `a.gamma_inverse` fixes its inverse as the
open-unit adjunction transpose. The open functors, ring restriction and total tensor
are those already supplied by the dependency `lem-sf-open-tensor-normalization`.

Hypothesis and clause correspondence:

- Scheme X, open U and open immersion j are `d.X`, `d.U`, `d.j` in `d : Input m`.
  `Input.j_open` and its registered instance give `IsOpenImmersion d.j`.
  The package also retains the base-change square of the normalization dependency;
  no g, gU, primed open, or pullback enters the equation. These data impose no new
  hypothesis on the item: every j admits the identity base-change square, with
  X'=X, U'=U, g=id, gU=id, S=R and the identity structural coefficient map.
  Normalization existence supplies t, o, a for that square. Quantifying over all
  packages also makes the result independent of these irrelevant choices.
- The arbitrary strict ring sequence B is `d.R : Sheaf (topology m d.X) CommRingCat`.
  For `m = Mode.systems`, `Site m X = ℕ × X.ProEt`, with vertical covering topology.
  Its presheaf direction makes the coefficient arrows B(n+1) -> B(n). The level
  numbered 0 is the node's B_1; this is just reindexing. Nothing requires transition
  maps to be flat, surjective, or equivalences. For `m = Mode.ordinary`, the site is
  `X.ProEt` and R is one arbitrary commutative ring sheaf.
- Strict semilinear modules are the existing intrinsic `Mod d.R` on this ringed
  diagram site, not a product of module categories. A module morphism commutes
  with every horizontal restriction and therefore every actual coefficient map.
  This is the vertical-site interpretation in `semilinearDerivedSections`.
- Ordinary unbounded derived categories are `Der d.R` and
  `Der (restrictRing m d.j d.R)`, abbreviating `DerivedCategory (Mod ...)`.
  No boundedness, constructibility, degree-concentration or finite-Tor predicate
  occurs on either input.
- J_j is `o.opens.jShriek = o.opens.extension.ordinary.mapDerivedCategory`.
  The recorded `OpenExtension` includes additivity and finite-limit/colimit
  preservation. P_j is `o.opens.jStar = (restrict m d.j d.R).mapDerivedCategory`;
  the dependency's `restriction_exact` supplies its exactness. On the diagram site
  these are termwise open extension and restriction.
- Derived system tensor is `o.tensorX.functor` and `o.tensorU.functor`. These are
  the dependency's `TensorModel` objects, with representative comparisons to the
  existing signed direct-sum `total` tensor on `resolving R`: K-flat complexes
  with flat terms. These are resolving models, not additional hypotheses on M,N.
- The normalized delta is exactly `a.gamma.hom.app (M,N)`. In particular the
  first arrow of the left composite is delta_(M,N[r]). Its source is
  `o.tensorX.functor.obj (o.opens.jShriek.obj M, N⟦r⟧)`.
- The canonical cochain shifts are the existing `TensorShifts o.tensorX` and
  `TensorShifts o.tensorU`. The initial conjunction asserts that they exist;
  the remaining universal instance binders assert the square for every such
  normalized choice. Thus the assertion cannot become vacuous by lacking shifts.
  `TensorShifts.second` is `tensorShiftSecond`, whose representative equation
  uses `CochainComplex.mapBifunctorShift₂Iso`, not an unspecified shift isomorphism.
  That Mathlib map multiplies first-degree a by `(a*r).negOnePow`, the prescribed
  (-1)^(r*a). The structure also contains the standard first-slot shift and the
  ordinary coherence data; this is the already existing cochain shift interface.
- For arbitrary `M : Der (restrictRing m d.j d.R)`, `N : Der d.R`, `r : ℤ`,
  s_F is `(((Functor.curry.obj o.tensorX.functor).obj
  (o.opens.jShriek.obj M)).commShiftIso r).hom.app N`.
- s_H is the three specified steps written after delta on the left: use
  `o.opens.jStar.commShiftIso r` inside the second tensor slot, apply the
  normalized second-slot comparison of `o.tensorU`, then apply
  `o.opens.jShriek.commShiftIso r`. The expression is the canonical shift of
  J_j(M tensor P_j(-)), with no arbitrary exact-functor comparison introduced.
- The equality has exactly the node's order: delta_(M,N[r]) followed by s_H equals
  s_F followed by `(a.gamma.hom.app (M,N))⟦r⟧'`, in the ambient derived category.
- Naturality in M,N comes from the existing natural isomorphism `a.gamma` and
  the bifunctor `CommShift₂Int` structures, including naturality in maps of the
  fixed first input. It is not a family of arbitrarily chosen objectwise arrows.
- Compatibility with actual coefficient transitions is inherent in this equality
  of morphisms in `Der d.R` on the ringed diagram site. No inference from equality
  of evaluated derived morphisms is made.
- The same universally quantified theorem with mode ordinary gives the entire
  single-ring clause. Any finite constant ring, including O_E/varpi_E^n, is a
  specialization of that arbitrary ring sheaf. No finiteness hypothesis is needed.

Dependency declarations read and reused (full source signatures/docstrings inspected):

- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  its topology, used through the normalization site's ordinary mode.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`, the canonical
  ordinary-derived strict-system interpretation, imported as a statement dependency.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `HasDerivedCategory`, used via the existing `Der` abbreviation.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its identification with
  the live `IsAcyclicTensorKFlat`; the latter is used by `resolving`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  `mapBifunctorShift₂Iso` and `ι_mapBifunctorShift₂Iso_hom_f`.
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.openTensorNormalization` and its public data module's
  `OpenTensorNormalization.Mode`, `Input`, `SiteSquare`, `Operations`, `Assertion`,
  `Assertion.gamma`, `Assertion.gamma_inverse`, `OpenDerived.jShriek/jStar`.
- The normalization package publicly reuses `Sheaf.Paper.RingedProjectionRestrictionData`:
  `AlgebraicGeometry.Scheme.ProjectionRestriction.Mod`, `Der`, `TensorModel`,
  `TensorShifts`, `tensorShiftSecond`, `total` and `resolving`. These are existing
  dependency interfaces; no substitute definitions are introduced.

All stated proof dependencies are imported plainly when not already public statement
imports: `FlatOnSite` (`IsFlatOnSite`), `KFlatResolutionIndependentCoefficients`
(`exists_isKFlatResolutionIndependentCoefficients`), `RingedSliceTensorGenerators`
(`exists_ringedSliceTensorGenerators`), `Adjunction.Limits`
(`Adjunction.leftAdjoint_preservesColimits`), and
`RingedTopoiCanonicalTensorPullbackOfUniverses`
(`CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`).
The theorem docstring carries all six proof steps with the matching node IDs.

Sources checked: Stacks sites-cohomology.tex, lemma-j-shriek-and-tensor (0GL1);
more-algebra.tex, item-shift-tensor (0FNH); and the latest blueprint's
sk-thm-purity-transport.proof.md Step 2 and fix-prop-coherence.md. The source uses
unbounded ordinary derived tensor. The sign agrees with the inverse direction of
Stacks' total-shift comparison, since the scalar is its own inverse.

Edge cases checked before and after writing:

- Empty open: extension has zero source and both composites have zero image.
- Identity open: the normalized delta becomes the ordinary tensor identification;
  both sides use the same canonical second-slot comparison.
- r=0 and all negative r: r has type ℤ; the sign is Mathlib's integer negOnePow.
- Characteristic 2: the sign becomes 1 on both paths, without excluding the case.
- Zero M or N: the equation is between the corresponding zero tensor maps.
- Arbitrary unbounded complexes: only the ordinary unbounded derived category
  appears. Flat/K-flat conditions are on resolving models, not on the inputs.
- A nonflat tower, e.g. constant ring sheaves Z/4 -> Z/2, is permitted by `Input.R`.
  The tensor and equality take place in the strict diagram module category itself.
- Site objects retain universe u+1 and site morphisms universe u, exactly as the
  recorded normalization interface. Coefficients have the ambient universe u+1;
  no equality of site object/morphism universes is imposed. Larger coefficient
  sets can be accommodated by enlarging the ambient universe/size convention.

Searches made with the prescribed tools:

- msearch leanfinder: "Open extension by zero tensor projection comparison commutes
  with signed shift for strict semilinear inverse systems". Eight unrelated
  inverse-system and profinite results; no open-tensor shift theorem.
- msearch loogle: "CochainComplex.mapBifunctorShift₂Iso". Eight results, including
  that canonical sign map, its summand formula and naturality; no normalized open
  derived tensor square. Reused those existing shift interfaces.
- msearch grep: "open.*[Tt]ensor.*[Ss]hift|tensor.*[Pp]rojection.*[Ss]hift".
  No Mathlib matches.
- msearch leansearch: "Extension by zero tensor projection formula isomorphism
  commutes with signed second shift of cochain complexes". Eight results on
  generic cochain shifts and resolutions; none states the item's square.
- rg in lean/WeilConjectures and lean/Sheaf for the item ID and open-tensor-shift
  names: no identical theorem. Nearby scheme-derived monoidal and completed
  tensor shift modules concern different coefficient categories or operations.
- grep -rn of the item ID in lean/WeilConjectures: no match.
- rg for the chosen declaration name in Mathlib, the upstream name index,
  WeilConjectures and Sheaf: no collision.

Verification: scompile.py compiled this file both as the sandbox module and at
its intended library path, with no errors or warnings (13.6 s and 10.2 s).
No STATEMENT-DISPUTED issue or node fault found.

## Second reading by Q11

This is the dispatcher's worker self-check; independent maintainer review follows
delivery. I reread the node and the complete module against the correspondence above.
The first draft compiles without changes. In particular, I checked the direction of
both gamma and the shift maps: the equation starts at J(M) tensor N[r] and ends at
J(M tensor P(N))[r]. The restriction shift must occur inside tensor before the
second-slot comparison; the extension shift must follow its image under J. Both are
present. The right side shifts gamma itself, not merely its source or its cohomology.
The existential nonemptiness clauses ensure the universal normalized-shift binders
cannot hide a missing construction. The ordinary and systems modes are both
universally covered, and transitions are carried by actual ringed-site morphisms.
No theorem was proved, no definition was copied, and no hypothesis on transition
flatness, degrees, Tor amplitude, or nonempty open was added.
