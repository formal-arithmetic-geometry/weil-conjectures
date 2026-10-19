## Worker report

The module `Sheaf.Paper.BoundedSiteAdjunctionTranspose` states
`AlgebraicGeometry.ProEtale.boundedSiteAdjunctionTranspose` and its naturality.
It uses the actual canonical compactification site comparison, defines the specified
Hom-chain function, packages that function as an equivalence using its bijectivity,
and defines the relative counit as the inverse transpose of identity. Every theorem
has whole proof `sorry`; the other declarations have real data. All four postponed
statements are clauses or necessary intermediate domain assertions of this DAG node,
and their docstrings contain the six-step natural-language proof.

Hypothesis-by-hypothesis correspondence:

- The global finite-field and coefficient datum, ell distinct from p, the finite
  subextension in its fixed algebraic closure, the uniformizer quotient and n >= 1
  are exactly `P : WeilConjectures.PurityFiniteSetting.{u}`. The ring is
  `P.Coefficient`, the existing ULift of `P.Ring = O_E/(varpi_E^n)`.
  `boundedSiteCoefficientFinite` obtains finiteness from
  `Padic.finite_coefficientExtensionRing` using `P.level_pos`.
- `X Y : Scheme.{u}`, structure maps `aX aY` to `Spec (.of P.field.k)`, and
  `LocallyOfFiniteType` plus `QuasiCompact` for each map say finite-type k-schemes.
  There is no absolute separatedness assumption on either scheme.
- `f : X ⟶ Y`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` and
  `hf : f ≫ aY = aX` say separated finite-type k-morphism.
- `c : Compactification f` supplies the specified open immersion `c.i`, proper
  morphism `c.g`, scheme `c.Z` and factorization. `d : ℕ` and
  `hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)` encode exactly the nonnegative
  integer dimension bound, including dimension minus infinity of the empty scheme.
- Ordinary constant-ring module derived categories are
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u+1} P.Coefficient))`
  and the same construction for `Scheme.ProEt.topology T`. These are the recorded
  fixed-ring presentations of the constant-ring module categories, with the existing
  coefficient realization equivalences. They are not condensed or completed categories.
- `H` and `adj : Etale.rightDerivedLowerShriekOfCompactification ... c ⊣ H`
  specify the chosen ordinary etale right adjoint f^times and its actual adjunction.
  The named pro-etale compact-support functor is
  `rightDerivedLowerShriekOfCompactification ... c`; both functors use the same c.
  The right functor in every type is literally `C_X H U_Y`, as required by the node.
- `J` and `K` belong to the etale `DerivedCategory.Plus`, and
  `hHK : DerivedCategory.TStructure.t.plus (H.obj K.obj)` is exactly the additional
  stated lower-boundedness condition on f^times K.

Clause-by-clause correspondence:

- B_(f,J) is `(compactSupportSiteComparison P.Coefficient c).inv.app J`.
  Read the construction in `CanonicalCompactSupportSiteComparison.lean`: its plus
  version pastes `fixedComparisonDirectImageMatePlus` with
  `properOpenSiteExtensionIso`, and its ambient version only inserts the canonical
  plus-to-ambient compatibility isomorphisms. Thus this is precisely Rp_*(e_j)
  after the named proper counit mate, with the direction required in the node.
  Its invertibility and naturality are part of the existing natural isomorphism;
  no new independently chosen B is introduced. The already landed node
  `lem-sf-class-compact-support-comparison` was added to stmt_deps to cite this object.
- `boundedSiteTranspose` is exactly Phi: precompose by B, apply the comparison
  adjunction Hom map (`U_Y` of that map after eta), apply `adj.homEquiv`, then
  apply `C_X.map`. It is a concrete function with no arbitrary adjunction datum.
- `boundedSiteRightAdjoint_plus` states the necessary lower bound of H U_Y L
  for every bounded-below pro-etale L, the intermediate assertion of proof step 2.
  `boundedSiteRightAdjointPlus` merely bundles this actual object with its bound.
  `boundedSiteTranspose_bijective` states that Phi is bijective on the exact
  bounded etale-origin domains. `boundedSiteHomEquiv` is `Equiv.ofBijective` of
  this fixed function, so the pending theorem determines its inverse uniquely.
- `boundedSiteRho` is `C_X.map (H.map (derivedComparisonAdjunction.unit.app K))`,
  not an arbitrary isomorphism between the same endpoints. The first conjunct of
  the main theorem asserts this specific component is invertible.
- `boundedSiteCounit` applies the inverse specified Hom equivalence to identity
  at the actual object C_X H U_Y L. Its source uses that object's identity
  etale-origin witness, with its lower bound supplied above. This is the relative
  counit of the prescribed Hom chain, rather than an independently selected map.
- The second conjunct is B_(f,HK) followed by F_p(rho_K) followed by
  `boundedSiteCounit` at C_Y K, equal to `C_Y.map (adj.counit.app K.obj)`.
  This is exactly the displayed normalized counit equation, in Lean's left-to-right
  composition order.
- The last conjunct quantifies every `a_e` and `a_p`, assumes exactly
  `B_(f,J) ≫ a_p = C_Y.map a_e`, and concludes that the specified pro-etale
  transpose equals `C_X.map (adj.homEquiv ... a_e) ≫ boundedSiteRho ...`.
- `boundedSiteAdjunctionTranspose_naturality` explicitly states source naturality
  of Phi for every map J' -> J, target naturality for every bounded-below L -> L',
  and naturality of rho for every bounded-below K -> K'. Thus the comparison is
  natural in J,K on exactly the stated domains. The function underlying
  `boundedSiteHomEquiv` is definitionally Phi. No ambient pro-etale exceptional
  adjunction on all unbounded objects appears in any declaration.

Dependency declarations read and used (including canonical presentations):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`, their ring instances and `.level_pos`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, and `IsSeparated`.
- `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement`;
  its imported `Compactification.Defs` supplies `Compactification` and its fields.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the standard module-sheaf
  derived categories described in its docstring; the recorded torsion predicate is
  not imposed on the input, which would unnecessarily restrict the node's domain.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the module-sheaf realization
  and existing fixed-ring presentation (`finiteCoefficientRealization`,
  `finiteCoefficientEtaleRealization`, and their equivalence statements).
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`; its underlying ambient functor is
  `(comparisonUpperStar ...).mapDerivedCategory`, abbreviated by the existing D notation.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification`; the corresponding existing
  pro-etale functor is `ProEtale.rightDerivedLowerShriekOfCompactification`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `Scheme.sfIntrinsicCompactSupport`,
  read as the intrinsic-coordinate form of the same proper/open construction.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`, the source of
  the chosen etale adjunction, not an added assumption of existence.
- `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`:
  `sfFiniteExceptionalFixed` and `sfFiniteExceptional`, the recorded comparison
  composite in fixed and intrinsic coordinates. Here H is the chosen etale
  adjoint named by this node, so its specified composite is written explicitly.
- `Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass`:
  `ComparisonClassAdjunction` and `exists_comparisonClassAdjunction`. The old
  record's normalization references an older, arbitrarily selected proper comparison.
  We do not identify it with the canonical B. Instead the item constructs precisely
  its explicitly prescribed Hom chain from the named canonical B. Boundedness and
  full faithfulness supply bijectivity, independently of that earlier choice.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`, its invertibility and counit normalization.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso` and its coherence theorem.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit`, `compactSupportComparisonUnit`;
  the imported `derivedComparisonAdjunction` supplies the actual ambient unit,
  Hom map and counit, used only with the specified bounded exceptional domains.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparisonPlus` and `compactSupportSiteComparison`.
- Proof imports also retain `proper_basic`, exact etale extension by zero,
  `sfIntrinsicExtensionByZero_exact`, and `comparisonPullbackExact` from the recorded
  proof dependencies. Their source statements and proof plans were read.

Edge cases checked before writing: empty X or Y (no nonemptiness assumption);
empty compactification (dimension -infinity satisfies the dimension hypothesis);
d = 0 and coefficient level n = 1; zero complexes and zero morphisms;
identity compactification and identity etale-origin witness; bounded-below complexes
unbounded above; objects lacking constructibility; X,Y not separated over k.
The site object universe remains u+1 and its morphism universe u; coefficient and
module universes are the existing u+1 lift, with no extra universe equality.

Searches:

- `msearch.py ... leanfinder "Comparison between etale and proetale compact support
  adjunction transposes with canonical counit mate"`: eight unrelated condensed
  adjunction hits; none states this geometric normalized comparison.
- `msearch.py ... loogle "CategoryTheory.Adjunction.homEquiv_counit"`: one exact
  abstract adjunction formula; useful algebra but no site/compactification result.
- `msearch.py ... grep "homEquiv_counit|ofNatIsoLeft" CategoryTheory/Adjunction`:
  22 abstract transport/counit hits; no match for the complete statement.
- `rg` of upstream `WeilConjectures` and project `lean/Sheaf` for bounded transpose,
  this node id and `compactSupportSiteComparison`: no existing complete statement;
  found the canonical comparison module, reused rather than redefined.
- `rg` for all proposed `boundedSite...` names in both source trees: no collisions.
- Read Stacks `categories.tex`, lemma-transformation-between-functors-and-adjoints
  (Tag 0B65), and the current main-20261015 blueprint's
  `thm-sf-ambient-adjoint-class.md` and its proof, including the displayed bounded
  Hom chain and its lower-bound argument. The current server source of
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` was read using
  `scompile.py --source` because the older upstream checkout does not contain it.

No statement correction, new definition node or dependency replacement is required.
The added auxiliary definitions belong to this node's explicitly specified Hom map,
rho, and relative counit, and are all listed in lean.declarations.
The maintainer supplies the independent review; this worker does not claim to have
performed an independent second reading.

Validation: prescribed `scompile.py` compiled the module cleanly after application
parentheses were fixed; only file-level compilation was used. The final delivery
preflight is run through `deliver2.py`, including its own fresh compile.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
