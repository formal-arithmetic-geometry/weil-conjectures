## Worker report

The module `Sheaf.Paper.CoordinateTowerNormalizationInduction` states the ordered
normalization induction, with arbitrary supplied maps u_r and the actual
canonical comparison maps. Its main declaration is
`AlgebraicGeometry.ProEtale.CoordinateTowerNormalization.coordinateTower_normalization_induction`.
No theorem is proved. The auxiliary postponed assertions are
`zero_successor` (the coordinate identity), `target_properties` (the finite
Tate-power input calculation of proof Step 1), `thetaStepRaw_target`
(the computed codomain of the actual recurrence composite), and
`projectionGammaRaw_target` (the computed target of the recorded gamma,
including its identity normalization). Their docstrings give their
complete natural-language proofs. All definitions have explicit data.

Hypotheses and clauses:

- The finite field, its fixed algebraic closure, ell distinct from the
  characteristic, and the finite coefficient extension are the fields of
  `P : WeilConjectures.PurityFiniteSetting.{u}`. `setting P n` uses level `n+1`;
  this includes every positive coefficient level, with no ramification
  divisibility hypothesis. The coefficient ring is the recorded quotient's
  canonical universe lift, not a different ring.
- The base scheme and structure morphism are `B` and `aB`. The instances
  `LocallyOfFiniteType aB`, `QuasiCompact aB`, and `IsSeparated aB` say exactly
  separated finite type over the fixed field. No smoothness of B is assumed.
- `c : ℕ` includes dimension zero. The schemes and maps are the existing
  `iteratedAffineLine B r`, `iteratedAffineLineProj B r`, and
  `AffineZeroPurity.zero B r`. `lastProjection` and `lastSection` discard and
  kill the final coordinate in this same ordered model. `zero_successor`
  spells out the coordinate composition equality.
- `coefficientUnit` and `tatePower` are typed references to the existing
  unit and target, fixing the canonical ambient derived-category instance once.
  Their data are exactly `AffineZeroPurity.unit` and `.target`, respectively.
  They introduce no new object or mathematical construction.
- W_r is the existing `target P n (iteratedAffineLine B r) r`, the ordered
  r-fold tensor product of the compared shifted Tate line with the coefficient
  unit. Thus W_r=A_X(r)[2r], including the empty tensor unit at zero.
- `gamma P n B aB r` specializes the recorded
  `AffineSpacePurity.affineSpacePurityComparison` to the coefficient unit with
  its actual constant ordinary antecedent. `targetSourceIso` is the canonical
  unit-pullback identification; it accounts for the source W_r. No purity
  isomorphism has been chosen. `projectionGammaRaw` retains the actual recorded
  gamma with its computed target, and `projectionGammaRaw_target` exposes that
  target as Rp_r!A_B. `projectionGamma` uses only this endpoint transport and
  restores the canonical exceptional identity normalization at dimension zero.
- `hline : LineLaw ... c` asserts invertibility and naturality of exactly the
  c affine-line comparisons, on bounded-below inputs carrying arbitrary
  bounded constructible finite-Tor ordinary antecedents and comparison isos.
  The equation quantifies over every derived morphism between two such
  inputs. The latter class is precisely the finite-coefficient D^b_ctf class;
  ordinary antecedents are a presentation, not an extra restriction.
- `u : Orientations ... c` supplies exactly the maps u_r, indexed by Fin c,
  with no initial invertibility condition. `hu` is u_r followed by S_r(v_r)
  and the canonical contraction S_r Q_r -> id, equal to the identity of W_r.
  `targetLineGamma` uses the actual comparison and the canonical `stepSource`
  identification. `lineCollapse` is the inverse conjugate of the fixed compact
  compositor, followed by q_r s_r=id and the normalized identity adjunction.
- `ordinaryTarget` is the explicit Rnu_* of W_r, not an antecedent chosen from
  existence. `target_properties` verifies finite-Tor constructibility, the
  same property of this ordinary antecedent, and invertibility of the actual
  comparison counit. `targetComparison` is that counit made into an iso.
- `closedCompositionInverse` constructs d_r^-1 by the same
  `compositionInverse`, followed by equality transport along `zero_successor`.
  `thetaZero` is the identity under the canonical exceptional identity
  normalization. `thetaStep` uses `mapComposition` to type the same three-arrow
  composite once; `theta` applies the already recorded `orderedRec`.
  This is exactly the finite recurrence in the node:
  theta_r, then Z_r(u_r), then d_r^-1. Its bound proof only selects u's index.
- The first conjunct concludes invertibility of each actual gamma_r for
  r<=c. It gives the explicit witness iso from W_r to its target and identifies
  its hom with `targetSourceIso.hom` followed by that gamma_r, together with
  finite-Tor constructibility of W_r. This is the stated finite-Tor witness.
- The second conjunct is b_0 theta_0=1; the third is the stepwise equality
  b_(r+1) theta_(r+1)=b_r theta_r for every r<c. Lean composes arrows left to
  right, so these appear as `theta ... ≫ normalization ...`. The fourth
  conjunct is the terminal b_c theta_c=1.
- The fifth conjunct is the transpose formula. `classMap` has the actual
  source Rz_*A_B and is the closed exceptional adjunct of theta_c precomposed
  with the inverse canonical proper comparison Rz_!A_B -> Rz_*A_B.
  Closed direct image is exact, so this is z_*A_B in the node.
  `augmentation` is the projection adjunct of gamma_c.
  `sourceIdentification` begins with the same inverse proper comparison under
  Rp_!, then uses the actual compact-support compositor, p_c z_c=id, and its
  canonical identity comparison. Equality with its
  hom says exactly that the composite is identity under that comparison.
- The last conjunct assumes all supplied u_r invertible and concludes every
  theta_r invertible and b_r=theta_r^-1. The explicit existential instance
  `ht` binds the inverse without inserting an invertibility hypothesis.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and
  its recorded coefficient constructions.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.Proper`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, and the properness of
  closed immersions. `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded finite
  Tate coordinates, reexported through the existing comparison modules.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its public
  imports: the actual constructible exceptional operations, with
  `rightDerivedUpperShriekHomEquiv` on the origin class and its counits.
- `Mathlib.CategoryTheory.Adjunction.Basic` and `.Mates`: `Adjunction.comp`,
  `Adjunction.id`, `conjugateEquiv`, and their pasted unit/counit conventions.
- `Sheaf.Paper.AffineSpacePurityComparison`: `affineSpacePurityComparison`,
  `sourceReassociation`, `lineComparison`, `lineSource`, `exceptional`,
  `compositionInverse`, and the coordinate geometry interfaces.
- `Sheaf.Paper.AffineLinePurityComparison`: `affineLinePurityComparison`,
  reexpressed by the recorded `lineComparison` wrapper.
- `Sheaf.Paper.AffineSpaceCoordinateBoundaries` and `.AffineSpaceThomMap`:
  `setting`, `unit`, `zero`, `target`, `target_plus`, and `unit_origin`.
- `Sheaf.Paper.AffineSpaceZeroSectionPurity`: only its shared constructions
  `targetSourceIso`, `gamma`, `normalization`, `identityUnit`, `collapse`, and
  their coordinate/identity obligations. Neither `zeroSection_purity` nor
  either of its corollaries is used. There is one definition of each notion.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `originCompositionAmbient`, `originCompactSupportCongr`, and
  `originCompactSupportId` fix the same coherent compact-support comparisons.
- The stated proof dependencies are imported plainly. The recently created
  proof-only node `lem-pur-closed-section-compact-origin` has no Lean record or
  mathlib match, hence no module to import. The needed source isomorphism is
  nevertheless constructed explicitly here from the already recorded
  compositor and identity comparison; no statement is made conditional on an
  unavailable helper or an arbitrary source isomorphism.

The shared-construction import of `AffineSpaceZeroSectionPurity` means adding
this file as a proof import back to that module would form an import cycle;
that proof-import edge must be omitted under stages/2-statements.md section 3,
rule 7. No theorem from that parent module supplies any part of this theorem.
A later proof refactor can relocate its shared constructions without duplicating
or changing them. No source file is modified by this delivery.

Edge cases checked: c=0 gives an empty u family and vacuous affine-line law,
the actual identity-normalized theta and gamma, and the identity transpose.
c=1 gives exactly the supplied line evaluation; c=2 gives its ordered two-step
composition. The empty base gives zero objects and their unique identity maps.
The base can be nonreduced or disconnected. n=0 represents coefficient level
one; no positive level or ramification case is excluded. All schemes remain in
universe u and the small pro-etale module site in its recorded u+1 size.

Searches performed:

- msearch LeanFinder: `Ordered affine space coordinate tower exceptional
  inverse image normalization induction zero section purity`. Eight hits,
  all scheme-normalization declarations, no purity normalization induction.
- msearch Loogle: `CategoryTheory.Adjunction.comp,
  CategoryTheory.Adjunction.homEquiv`. One hit `Adjunction.comp_homEquiv`, a
  generic ingredient, not the stated ordered finite-coefficient induction.
- msearch grep, Mathlib/AlgebraicGeometry:
  `affine.*purity|zeroSection.*trace|coordinate.*normalization`. No hits.
- msearch LeanSearch: `Affine space purity ordered zero section normalization
  induction for exceptional inverse image`. Eight hits, concerning ordinary
  scheme normalization, affine space, and zero loci; none states this result.
- rg in lean/WeilConjectures and lean/Sheaf, by the exact item id,
  `coordinateTower`, `normalizationInduction`, `normalization_induction`, and
  the affine-purity/normalization vocabulary. The existing parent module
  supplies the canonical gamma and b constructions but only states purity for
  its specific Cartier orientations, not this arbitrary-u_r induction. The
  upstream smooth normalization lemma concerns a different trace construction.
  The existing declarations were reused; no matching full statement was found.

No statement correction, disputed assertion, new node, or dependency repair is
needed. The item's natural-language statement is unchanged. The existing
coordinate-boundary and Thom-target definition nodes are added to stmt_deps
because their recorded target, unit, and zero-section declarations are used.

Validation is recorded below after the final compiler and preflight checks.

Final per-file validation: the prescribed scompile.py compiled the delivered
module in sandbox mode (33.7 s) and its real library module mode (22.2 s).
Both passed with no errors or warnings, within the unchanged 60-second limit.
No Lake or global build was run. Diagnostic probes remain outside lean/ and
are not delivery files. The subsequent deliver2.py dry run supplies the
maintainer preflight and its required independent per-file verification.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
