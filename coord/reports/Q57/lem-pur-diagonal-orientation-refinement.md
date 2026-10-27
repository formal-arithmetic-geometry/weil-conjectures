## Worker report

The delivery states `WeilConjectures.PurityFiniteSetting.diagonalOrientationRefinement`
in `Sheaf.Paper.DiagonalOrientationRefinement`. The only postponed proof is this theorem,
whose proof is exactly `sorry`. The other declarations construct the specified arrows,
or package their equations as propositions and structures; none has postponed data.
Only the item's `lean` field changes. There are no new nodes, dependency repairs, or
statement corrections.

Source read: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-orientation/thm-pur-diagonal-dualizing-object.proof.md`, Step 2 and the
combining paragraph. Also read the item's nine accepted proof steps and all fifteen
statement dependencies, their records, and their recorded source declarations. The source
pulls vector purity back along zero and explicitly attributes canonicity and base-change
compatibility to diagonal base change, normalized DNC, and vector purity.

The namespace `OrientationRefinement` contains helpers belonging to this very comparison.
In particular it does not introduce a second section invariant, normal cone, Tate line,
or exceptional functor. `source`, `normal`, and `normalEtale` specialize the published DNC
section objects; `alpha` and `rho` specialize the affine-target dependency's actual arrows.
`delta` selects the unique DNC map fixed by the full published family equation.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| The fixed algebraic closure of F_q, coefficient prime distinct from p, finite extension E, A=O_E/(varpi^n), n>=1 | `P : PurityFiniteSetting.{u}`. Its `field`, `coefficients`, `extension`, `finiteExtension`, `level`, and `level_pos` give exactly these data. `P.Coefficient` is the standard size lift of this quotient. |
| Finite-type k-schemes X,Y and a k-morphism f | `X Y : Scheme.{u}`, `aX`, `aY`, their `LocallyOfFiniteType` and `QuasiCompact` instances, and `hf : f ≫ aY = aX`. |
| f separated and finite type | `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. |
| f smooth of pure dimension d>=0 | `(d : ℕ) [SmoothOfRelativeDimension d f]`; no positivity binder. |
| Every finite-type affine target open V | `V : Y.affineOpens` and `(V.1.ι ≫ aY).appTop.hom.FiniteType`. On the affine source this is precisely finite generation over k. The family D ranges over every such V, not one selected cover. |
| X_V and its map j_V | `(f ⁻¹ᵁ V.1).toScheme` and `(f ⁻¹ᵁ V.1).ι`, the recorded model of the target-base-change fibre product. |
| W_V, first projection, diagonal | `pullback (f ∣_ V.1) (f ∣_ V.1)`, `pullback.fst`, `pullback.diagonal`. |
| N_V, pi_V, zero section | `(pullback.diagonal (f ∣_ V.1)).ker.normalCone`, `Scheme.Hom.normalConeProj`, and `.normalConeZeroSection`. These are the published extended-Rees normal object and its augmentation, canonically compared with the recorded associated-graded relative Spec. |
| Normal bundle is rank d with its zero section | `Chart.vectorModel : HasVectorModel ...` includes a rank-d locally free module and an isomorphism preserving projection and zero. This makes the subsequent normalization over all models nonvacuous, including d=0. |
| omega and C(g,s)=Ls*omega_g | `omega` is the canonical nu* presentation of the ordinary dualizing complex; `source` and `normal` use the dependency's actual `Dnc.sourceSection` and `Dnc.normalSection`. `sourceComparison` and `normalComparison` retain the specified site and unit comparisons. |
| Specified rho and alpha | `rho` is `P.affineDiagonalRho`; `alpha` is `P.affineDiagonalAlpha`. Both are the dependency's fixed counit-mate maps, not existentially chosen morphisms. |
| Specified normalized delta | `delta` is `.exists.choose` of `Dnc.existsUnique_dncInvariance`. Its determining equation includes all finite-type base changes and all family trivializations. This is a choice from uniqueness, not bare existence. |
| beta is zero pullback of vector purity followed by finite Tate pullback | `Chart.betaEtale` is required to satisfy `BetaNormalized`. For every vector-bundle model preserving projection and zero, its inverse, followed by the actual smooth section exchange, equals `vectorBetaInverse`: inverse Tate pullback followed by zero pullback of the integration adjunct. Inverting is exactly the stated beta. `beta` transports this same map through `Dnc.normalComparison` and nu*. Thus the statement concerns specified purity, rather than mere existence of an orientation. |
| Target A_XV(d)[2d] | `P.diagonalTwistEtale ... d` and its pro-etale realization `P.diagonalTwist ... d`, defined by the existing ordered tensor of shifted finite root lines. `FiniteTateSiteDescent` identifies this presentation with the actual finite pro-etale twist. |
| Lj_V* A_X(d) canonically identifies with A_XV(d) | `tate P (f ⁻¹ᵁ V.1).ι aX d` is that comparison, with the shift already incorporated. The same construction is used for every smaller-open comparison in the theorem. |
| theta=beta delta alpha^-1 rho | `theta` is literally `rho ≪≫ alpha.symm ≪≫ delta ≪≫ beta`. Every factor is an `Iso`. |
| Inclusion a:X_V' -> X_V | `inclusion f h = X.homOfLE (f.preimage_mono h)`. |
| Canonical identification of section pairs | `Geometry.product` has both specified projection equations, its diagonal equation, and the Cartesian first-projection square. The projection equations uniquely determine the product map; the Cartesian square identifies the stated fibre product with W_V'. |
| Normal-bundle pullback, including zero | `Geometry.normal_cartesian` and `zero_eq`. `normal_eq` fixes the map by its composite with the closed zero-fibre inclusion: the other side is the coefficientwise published `SectionReesBaseChange.pairMap`. Monicity fixes this normal map uniquely; no unspecified normal-bundle automorphism is allowed. |
| rho,alpha,delta,beta restrict to their specified counterparts | The four equations of `Compatible`, in that order. `eF`, `eC`, `eN` use the actual smooth exceptional exchange, with the source and normal canonical site comparisons inserted. `tate` is the root-normalized Tate comparison. |
| theta restricts to theta_V' | `Agrees`, and equivalently `restricted` equals the smaller theta. The first conjunct quantifies this over every affine inclusion. |
| Compatible with further affine restriction | The second conjunct is an explicit equality between `restricted` for `h₂.trans h₁` and the successive restriction, with `sourceComposition`, functorial inverse image and `tate` inserted. |
| Every overlap has a cover by finite-type affine opens | The third conjunct's supremum of all finite-type affine subopens contained in `V₁.1 ⊓ V₂.1` equals that intersection. This is an arbitrary cover; it does not assume the intersection affine. |
| On every common affine refinement both orientations equal theta_W | The last two equalities use the same `D W hW` and assert each restriction equals exactly its four-factor theta. |
| No absolute separatedness | There is no `IsSeparated aX` or `IsSeparated aY` binder. The affine-target geometry supplied in each `Chart.geometry` is a conclusion. |

Dependency declarations used (and modules read):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its coefficient
  quotient and size lift. `FixedFinitePositiveCoefficientTwist` is the already published
  finite-positive interface of the coefficient-twist node: `diagonalExponent`,
  `diagonalTwistEtale`, `diagonalTwist`.
- Mathlib `AlgebraicGeometry.Scheme`, `Morphisms.FiniteType`, `Morphisms.QuasiCompact`,
  `Morphisms.Proper`, `Morphisms.Separated`, `Morphisms.Smooth`, and `OpenImmersion`:
  `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`,
  `SmoothOfRelativeDimension`, `IsOpenImmersion`. The proper-morphism dependency is used
  for its separated notion; properness is not imposed.
- Mathlib `CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections
  and universal property; scheme `Restrict` supplies the equivalent inverse-image-open model.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its Data module:
  `ConstructibleExceptionalCoefficients.System`; the finite operation is the specified
  nu* / ordinary adjoint / Rnu_* transport, not an assumed ambient adjoint.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`, in the intrinsic
  realization. The DNC interface supplies its fixed-module realization with explicit
  comparison isomorphisms; no new pullback operation is defined.
- `Sheaf.Paper.PuritySectionInvariantIntrinsic`: `sectionInvariantFinite`; the same
  object is used in the DNC finite realization and its comparison to fixed coefficients.
- `Sheaf.Paper.PurityNormalProjection`: `Scheme.Hom.purityNormalProjection` and its
  equality with `normalConeProj` for a section. The geometry uses this very normal cone.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded coefficient-twist
  interface, together with its finite shifted fixed-ring interface just named.
- `Sheaf.Paper.AffineTargetDiagonalDnc`: `AffineDiagonalGeometry`,
  `affineDiagonalRho`, `affineDiagonalAlpha`, `AffineDiagonalConclusion`,
  `affineTargetDiagonalDnc`. In particular its conclusion gives a unique normalized DNC
  comparison and the required separated finite-type chart domains.
- `Sheaf.Paper.VectorBundlePurity`: `vectorBundlePurity`,
  `VectorBundlePurityConclusion`; the unit value is fixed by integration and adjunction.
  `VectorPurityNormalization` supplies `purityTwistTransport`, and the imported vector
  integration module supplies the actual normalized trace transposed by `vectorBetaInverse`.
- `Sheaf.Paper.CartesianCoefficientTwists`: `spFiniteTwists_cartesian`,
  `SpSignedComparison` (zero, positive tensor, evaluation and derived comparisons), and
  `spTwists_cartesian`. Its nonnegative finite fixed-module comparison is realized by
  `vectorIntegrationBaseCoefficientPullback`; `tate` inserts `Dnc.pullComparison`.
- Proof imports are retained for the nine steps, including finite Tate site descent,
  cohomological smoothness, exchanges, Mathlib mate pasting, derived pullback composition,
  support comparison-pullback coherence, and the basic-open/localization declarations.
  `SectionReesBaseChange.pairMap` is the already constructed coefficientwise Rees map used
  to fix the normal restriction; its geometry data are not replaced by a fresh construction.

Edge cases checked before and after writing: d=0 uses the existing tensor-zero coefficient
unit and the same section maps; no primitive root or frame is selected. Every positive
coefficient level occurs, without any ramification-index divisibility hypothesis. Empty X,
empty affine charts, empty overlap, and the empty indexing subtype in the cover supremum
are allowed. X and Y may be nonseparated over k. The ordinary-etale comparison is carried
onto the actual pro-etale site; the scheme universe is u, the fixed module coefficient
universe u+1, and the small pro-etale site retains its distinct object/morphism universes.
Neither a general smooth orientation nor any downstream global diagonal orientation is
used to define beta. There is no dependency cycle through such a downstream orientation.

Searches actually run using `msearch.py Q57 lem-pur-diagonal-orientation-refinement`:

- LeanFinder: `The zero section pullback of vector bundle purity is a Tate twist and
  canonical diagonal orientations agree on affine target refinements` — eight results,
  including `Scheme.Pullback.diagonalRestrictIsoDiagonal`, affine-space coordinate maps,
  and open-cover affine-refinement object isomorphisms. These concern geometric diagrams,
  not the exceptional/Tate comparison and the four specified-factor equations.
- Loogle: `CategoryTheory.Functor.mapIso,
  AlgebraicGeometry.Scheme.Pullback.diagonalRestrictIsoDiagonal` — zero hits.
- Mathlib grep: `diagonalRestrictIsoDiagonal|sectionRestrictionIso|vectorBundlePurity` —
  three hits, the diagonal-restriction declaration and uses in Separated and
  FormallyUnramified. None states the item.
- LeanSearch: `Vector bundle purity zero section Tate twist diagonal affine restriction
  compatibility` — eight results concerning topological/manifold bundle zero sections and
  the restriction of a zero section in a ringed space; none is this statement.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  `orientationRefinement|orientation_refinement|diagonal.*refinement|diagonal-orientation-refinement`,
  and the item id in upstream sources — no existing statement of this item. The wider
  search for vector purity and normal/Tate comparisons found the already published
  affine-target, vector-purity and DNC interfaces used above. `DiagonalDncChartNormalization`
  concerns affine source-and-target coordinate charts and uses the downstream global
  orientation; it neither states all target-open refinement clauses nor is needed here.

Validation: server `scompile.py` compiled the sandbox and actual library module separately,
with no errors or warnings. The final signature has explicit variables and universe `u`,
with `autoImplicit false`. All lines are at most 100 characters.

## Second reading by Q57

I reopened the unchanged node statement and read the final module from its source and
normal objects through `BetaNormalized`, the four equations, the successive-restriction
formula, and the overlap supremum. This is the dispatcher's author's second reading;
no independent-agent review is claimed (the brief forbids starting agents). The
maintainer's independent review remains the delivery review.

The first draft exposed a typeclass-instance inference mismatch for the normal projection:
the normal-cone geometry theorem had to be assigned explicitly to
`SmoothOfRelativeDimension d q`, rather than leaving its projection expression inferred.
That repair changes no hypothesis or mathematical statement. I also retained the
coefficient-unit isomorphism after integration before taking the Brown adjunct: this
ensures its target is exactly the tensor-unit dualizing object used by the recorded
rho/alpha/DNC interface, rather than silently identifying two presentations.

In the final reading, the normal-model existence field prevents vacuous universal
normalization, and its projection and zero equations exclude arbitrary presentations.
Both projection equations in `Geometry` fix the section-pair restriction, while its
closed-fibre equation fixes the normal map. `Compatible` compares the four actual maps,
not just their source and target objects. The equality `Agrees` has the original global
omega source through `sourceComposition`; it is not an equality of unrelated local
orientation choices. The common-refinement clause uses all finite-type affine subopens
of the possibly nonaffine intersection, and both final equalities have the identical
smaller theta. No missing clause, changed hypothesis, statement dispute, or node fault
remained after this reading.
