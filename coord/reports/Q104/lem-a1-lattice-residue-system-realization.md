## Worker report

The delivery states `AlgebraicGeometry.Scheme.LatticeResidue.realization_exists` in
`Sheaf.Paper.LatticeResidueSystemRealization`. Its sole proof is `sorry`.
`Realization` packages precisely the simultaneous conclusions, and the theorem
asserts existence of this package. `Lattices` restricts the existing representation
category to free objects satisfying the existing continuous-integral predicate.
The two section helpers are actual sheafification-unit and limit-map applications;
no object is chosen from the theorem. No statement or dependency node is corrected.

Sources read: Bhatt--Scholze, Proposition 6.8.4(1), pp. 59--60 (including the preceding
Definition 6.8.3 and coefficient-limit formula), the integral case in Lemma 7.4.7,
p. 70, and Stanford L19, Proposition 1.1.9, third bullet. The first source identifies
locally free completed modules with normalized finite systems; the latter sources
identify finite levels with the finite quotient representations. The node's five-step
proof is reproduced in the theorem docstring, including the coefficient-presentation
comparison needed for the literal limit of constant sheaves.

Hypotheses and all clauses are rendered as follows.

- A scheme is `X : Scheme.{u}`. `[ConnectedSpace X]` includes nonemptiness, so no
  redundant nonempty hypothesis is added. `[IsNoetherian X]` includes locally
  Noetherian and quasi-compact, and `[X.IsSeparated]` is separatedness.
- The prime is `(l : ℕ) [Fact l.Prime]`. Invertibility is exactly
  `[∀ x : X, Invertible (l : X.residueField x)]`.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `x : Spec (.of Ω) ⟶ X`. The profinite model is `G : ProfiniteGrp.{u}`, its
  actions on `FiniteEtale.fiber x`, and `IsFundamentalGroup (FiniteEtale.fiber x) G`.
  This is the project's standing FUNDAMENTAL GROUP convention. The correspondence's
  `c.γ` identifies it with the automorphisms of the actual FLC geometric fibre functor,
  with evaluation topology; `flcFiber` publicly reexports that recorded functor.
- The finite extension is `E : Type (u+1)` with `Field E`, `Algebra ℚ_[l] E` and
  `FiniteDimensional ℚ_[l] E`. Its A, uniformizer, ideals and quotients are the
  recorded `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal` and `coefficientExtensionRing`. No arbitrary DVR or
  separately chosen ring action is substituted.
- A lattice is an object `V : Lattices l E G`. Its underlying object is the existing
  `Rep` (action by linear endomorphisms of a group is automatically invertible).
  `Module.Free A V.obj.V` and `Representation.IsContinuousIntegral` give freeness,
  finite generation and joint continuity for the maximal-ideal-adic topology,
  which is the uniformizer-adic topology. Rank r is `Module.finrank A V.obj.V`;
  finite free modules over this DVR have exactly that rank. No basis is retained
  as input data. All equivariant A-linear maps are representation morphisms;
  on finite free adic modules these maps are continuous.
- `tower : Lattices ... ⥤ LisseIntegralSheaf l E X` gives every positive finite
  level. Exponent n+1 is indexed by n, exactly as in the existing category.
  Its predicate gives finite local constancy, annihilation by π^(n+1), and
  normalized adjacent reductions. This is the existing A-linear presentation of
  A_n-module sheaves: annihilation makes the A_n action unique. No new sheaf category
  or private normalization predicate is introduced.
- `finite_free V n` strengthens finite local constancy to an explicit etale cover
  on which the A-linear sheaf is the constant `(A/(π^(n+1)))^r`. Since A acts through
  the quotient, these isomorphisms are exactly A_n-linear local rank-r charts.
- `fibre V n` maps Λ to the actual geometric module stalk. `fibre_quotient` makes
  this map the cokernel of multiplication by π^(n+1), so it gives the specified
  Λ_n-to-stalk isomorphism normalized by the actual quotient map, not an arbitrary
  module isomorphism.
- `monodromy` identifies the module stalk with the underlying set stalk by its
  values on all germs and specifies equivariance for the evaluation action of `c.γ`.
  The germ equation fixes the comparison uniquely. `discrete_continuous` says that
  the stabilizer of every image of a lattice vector is open. Cokernel surjectivity
  on modules makes these all residue vectors; for a discrete G-set this is exactly
  continuity of the joint action.
- For n≥j≥1 the transition is the functor map at `(homOfLE hjn).op` (indices are
  shifted by one). It is A-linear, hence linear for A_n→A_j. `fibre_transition`
  identifies it with the actual residue quotient. The functor laws give all identity
  and triple composition equations, including equality of indices.
- `transition_quotient` is the sheaf cokernel universal property for the actual
  transition at every pair of levels. Since its source is annihilated by π^n,
  this is exactly invertibility of its adjoint A_j tensor_[A_n] F_n→F_j. Iterated
  quotients have the same universal map from F_n; uniqueness of cokernels gives
  compatibility with the canonical tensor associator for every triple. This
  universal-property presentation includes the maps and their normalization,
  rather than asserting existence of unrelated scalar-extension isomorphisms.
- `completed` lands in `ringedSiteModules` over the literal recorded
  `completedIntegralCoefficientSheafUnrestricted l E X`, i.e. the limit of constant
  quotient ring sheaves, with the usual harmless ULift of coefficient universes.
- `projection V` is a cone over the actual coefficient comparison inverse image
  of the underlying abelian finite-level diagram. The public
  `supportSiteComparisonCoefficientPullback` is the Kan-extension/sheafification
  construction of the recorded site morphism, definitionally the abelian
  `ProEtale.comparisonUpperStar`. `limit_property` makes this cone limiting, so
  its vertex is precisely the inverse limit with these projections. Representing
  a limit by a limiting cone preserves its canonical projection normalization.
- `coordinate_action` fixes the B_X-action by those projections. Whenever the
  n-th residue of b is the constant residue of a, the projection of b times s is
  a times the projection of s. Arbitrary residue sections are locally constant
  and locally lift to A; this equation on every object therefore determines the
  full coordinate action. `integralConstant` and `residueConstant` are the actual
  sheafification units through the recorded constant-to-completion map.
- `rank` is the existing `SheafOfModules.IsFiniteLocallyFreeOfRank` predicate,
  with r as above; thus the completion has exactly the required local rank.
- `scalar_sections` specifies multiplication by each constant a on completed
  modules. `projection_quotient` says that the actual n-th projection is its
  cokernel for a=π^(n+1). This gives exactly N/π^(n+1)N ≅ ν*F_n, induced by the
  limit projection. Cone naturality gives compatibility with all transitions.
- `tower` and `completed` are functors; `fibre_natural` and `projection_natural`
  give the actual squares for each equivariant A-linear map. Identities and
  composition are their functor laws. The adjoint maps and quotient comparisons
  are characterized by the same quotient maps, so their naturality follows
  uniquely, with no extra choice of these comparisons. Morphisms to lattices
  of a different rank are included in the one category.

Dependency declarations read and used (the declaration docstrings and complete
signatures were opened, including the public data modules behind the records):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`, including its `Nonempty` field.
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian`, `IsNoetherian`.
- The convention node def-weil-scheme-morphism-properties collects notions only;
  separatedness uses `Scheme.IsSeparated` from Mathlib's Separated module.
- Mathlib.FieldTheory.IsAlgClosed.Basic and Mathlib.AlgebraicGeometry.ResidueField:
  `IsAlgClosed`, `Scheme.SpecToEquivOfField`; the point is written inline as recorded.
- Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber: `Scheme.flcFiber`.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite (publicly importing
  CoefficientExtension): `Padic.finite_coefficientExtensionRing`, the coefficient
  integer, uniformizer, ideal, quotient and transition constructions.
- Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`.
- Sheaf.Paper.GaloisLisseRepresentations and its GaloisLisseCorrespondenceData:
  `Scheme.galois_lisse_representations`, `GaloisLisseFiniteCorrespondence`,
  `galoisRepLinearAction`, `galoisUnderlyingSetSheaf`, `galoisUnderlyingFLC`.
  The latter two reuse the actual module and set stalks; no second monodromy is defined.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: existing tensor
  and scalar-change constructions, interpreted through cokernel universal properties.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses and public CompletedIntegralCoefficients:
  `integralConstantToCompletionOfUniverses`, `integralCoefficientSheaf`,
  `integralCoefficientSheafSystem`, `completedIntegralCoefficientSheafUnrestricted`.
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison: `proEtaleSiteComparison` and
  `proEtaleSiteComparisonModules`; its public coefficient construction is used
  via `supportSiteComparisonCoefficientPullback`.
- Proof imports include every recorded proof-dependency module: ExtensionIntegersDvr,
  GaloisLisseRepresentations (already public), FundamentalGroup.FiberEquivalence,
  CochainTensorUniverses (already public), LisseCompletedSystemComparison,
  Mathlib.CategoryTheory.Limits.HasLimits, IntegralCoefficientPresentationComparison.
  `limit`/`limit.π` and `IsLimit` are the actual general categorical constructions.
- Sheaf.Paper.LisseCompletedSystemData: the unchanged `LisseIntegralSheaf`
  category/predicate and existing `Representation.IsContinuousIntegral` are public.
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, read including its local generator clause.

Edge cases: zero lattice/rank 0 is included by `Module.Free` and finite generation;
its local model is `Fin 0 → A_n`, and every quotient is zero. Positive exponent 1
is n=0, so the residue field level is included while the zero exponent is excluded.
For equal indices a transition is the identity and the scalar is already zero on
its source, making the cokernel assertion correct. For n≥j≥i the functor laws and
quotient universal properties retain identities and associativity. All ranks and
maps between different ranks are included; zero morphisms are allowed. The empty
scheme is excluded exactly by `ConnectedSpace`. No characteristic other than the
stated invertibility restriction is imposed. The site retains object universe u+1
and Hom universe u, with coefficients/modules u+1. Increasing u includes arbitrary
finite coefficient extensions and lattices; there is no site object/Hom universe
identification and no vacuous test universe.

Searches actually run:

- msearch LeanFinder: "A continuous action of the etale fundamental group on a finite
  free integral lattice gives coherent finite residue sheaves whose proetale inverse
  limit is locally free". Eight results included `IsFundamentalGroup.toIsNaturalSMul`,
  `exists_lift_of_continuous` and etale algebra facts; no match for the full statement.
- msearch Loogle: `"Sheaf", "IsLimit"`. Twelve results included
  `PresheafOfModules.isLimitLimitCone`, `Sheaf.isSheaf_of_isLimit` and sheaf conditions;
  none includes lattice representations, residue normalization and completed freeness.
- msearch grep: `(lisse|[Ll]ocal[Ss]ystem).*(residue|[Cc]omplet|[Ii]nverse[Ll]imit)`.
  No Mathlib hits.
- msearch LeanSearch: "A continuous integral lattice representation gives coherent
  finite locally constant residue sheaves and a locally free inverse limit on the
  proetale site". Eight hits concerned locally constant condensed objects and their
  Kan extensions; none states the etale/proetale lattice realization.
- rg of lean/WeilConjectures and lean/Sheaf for the item id,
  `latticeResidue`, `LatticeResidue`, `lattice.*residue|residue.*[Rr]ealization`:
  no existing declaration of this statement. Broader lattice searches found
  algebraic ideal lattices and unrelated reciprocity facts. Galois finite and adic
  data and completed-system data were opened and reused, rather than restated.

The sandbox file passed scompile.py in both sandbox and library modes (8.5 and
10.6 seconds respectively) before the final explicit dependency-import audit.
The delivery dry run recompiles that final file. No definition contains sorry,
there are no unbound auto-implicits, and the theorem is the only postponed proof.

## Second reading by Q104

I reread the node statement, the source pages and the complete Lean file after
writing it. This is a same-worker second pass: the dispatch explicitly forbids
starting another agent; the maintainer performs the independent delivery review.
The rereading checked each paragraph against the fields listed above, rather
than merely the final existence signature. It found two elaboration faults:
`Rep.Hom.hom` is an intertwining map, so `fibre_natural` now uses its actual
`ModuleCat.ofHom ...toLinearMap`; the public site-comparison abbreviation lives in
`AlgebraicGeometry.ProEtale`, which is now opened. Both changes preserve the maps.

The comparison with the source specifically checked that the completed coefficient
ring is the limit of constant quotient sheaves and not silently the continuous-function
presentation; the limit is asserted with its actual cone, and the coefficient action
is fixed by residue projection equations. The finite-level isomorphism is normalized
by the map from Λ, whose cokernel is Λ/π^(n+1)Λ, and monodromy is constrained by
its values on germs. Transition adjoints, quotient comparisons and all their naturality
squares are consequences of the displayed universal properties of the actual maps;
no unrelated isomorphism or extra normalization assumption is used. The final pass
also checked rank zero, equal indices, exponent one and maps between different ranks.
No mathematical mismatch or statement dispute was found; no node statement changed.
