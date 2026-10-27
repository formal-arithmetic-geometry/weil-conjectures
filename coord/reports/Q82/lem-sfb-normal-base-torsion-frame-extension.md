## Worker report

The delivery states Deligne Lemma 3.5.2 over exactly the normal locally Noetherian
scheme and separated smooth finitely presented commutative group algebraic space
of the node. Source read: the primary PDF
https://numdam.org/item/AST_1985__127__131_0.pdf, printed pp.131 (1.1) and 140
(3.5.2). The current blueprint direct-image proof in
literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/
was also read. No statement correction or disputed statement is needed.

Hypotheses and clauses:

- The schemes are `S V : Scheme.{u}`. `[IsLocallyNoetherian S]` is the recorded
  Mathlib notion, equivalent to the affine-cover definition. `hnormal` states
  that each stalk is both a domain and integrally closed, without assuming S integral.
- `j : V ⟶ S`, `[IsOpenImmersion j]`, and `DenseRange j.base` express exactly the
  dense open immersion, including the empty-base case.
- `N : AlgebraicSpace S` uses the recorded fppf-sheaf category. The given group law
  is `H : CommutativeSpaceGroup N`, with its original natural multiplication,
  identity and inverse; it is not an assumed scheme model of N.
- `hsmooth` uses `MapIsLocally (@Smooth)` on `groupSpaceProjection N`.
  `hseparated` is the published `MapIsSeparated`, the representable closed relative
  diagonal. `hfp` consists of local finite presentation and quasi-compactness of
  the projection and its diagonal, the standard finite-presentation conditions.
- `hsemiabelian : HasSemiabelianSpaceFibres H` supplies group-preserving scheme
  models over geometric fields, each with the published
  `HasSemiabelianGeometricFibres`. That predicate gives the split torus kernel and
  fppf-surjective quotient to an abelian variety, with the actual group laws.
  Such geometric extensions are smooth and connected. This does not assert that
  N itself is a scheme. `habelian : IsAbelianOn H j` supplies a representing
  proper smooth group scheme on V with connected geometric fibres and the
  group-preserving model isomorphism: the abelian-scheme condition.
- `n : ℕ`, `hn : 1 ≤ n`, `hinvertible : ∀ s, IsUnit (n : S.presheaf.stalk s)`
  express positivity and invertibility on S. `r : ℕ` permits every nonnegative rank.
- `spaceTorsionSheaf H n` has actual section groups
  `ULift (AddSubgroup.torsionBy (Additive (N(T))) (n : ℤ))`. The cyclic action is
  Mathlib's `AddSubgroup.torsionBy.zmodModule`, transported through the explicit
  `ULift.ringEquiv`. Its restriction maps apply the given original group map.
  The only postponed construction obligation is the named sheaf-condition theorem;
  no data are chosen from an unproved existence statement.
- The first conjunct is `Mono` of the actual unit of the recorded
  `Etale.upperStarLowerStarAdjunction`. For module sheaves this is precisely
  injectivity (equivalently sectionwise injectivity) of N[n] into j_*j^*N[n].
- `α` is an isomorphism from the restriction of this sheaf to
  `torsionLabels V n r`, the actual constant sheaf of `(Z/nZ)^r`.
  Restriction is the recorded `Etale.localizationRestriction`; the published
  `upperStarIsoLocalizationRestriction` canonically identifies it with j inverse image.
  On a V-test scheme its sections are exactly N(T)[n], hence N_V[n](T).
- `β` is a morphism in the category of sheaves valued in `ModuleCat` over the
  lifted cyclic ring. `Mono β` is the required monomorphism.
  The displayed equation after applying `localizationRestriction` and
  `torsionLabelsRestriction` is exactly that it restricts to α.
- `∀ γ, ... → γ = β` gives uniqueness among all linear sheaf maps, and hence
  the asserted unique monomorphism. This matches step 6 of the node's proof.
- The final conjunct explicitly handles any base isomorphism `h : S ≅ S'` and
  group-preserving isomorphism `e : H.points ≅ (Over.map h.hom).op ⋙ H'.points`.
  `spaceTorsionTransport` applies e to actual torsion elements, followed by
  restriction of β' and `torsionLabelsRestriction h.hom n r`. The hypothesis
  says exactly that the transported extension has open frame α, and the conclusion
  says it equals β. In particular this applies to the extension on S' whenever h
  identifies the specified open frames. The comparison of labels is constructed
  from `constantSheafCompUpperStarIso` applied to the very same coefficient module;
  there is no label automorphism or arbitrary comparison map.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace` and its actual fppf
  sheaf functor, with representable diagonal and atlas.
- Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.smallEtaleTopology`,
  `Scheme.Etale`, `Scheme.Etale.forget`.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`.
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs:
  `Etale.localizationRestriction`, `Etale.upperStarIsoLocalizationRestriction`.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `constantSheaf`.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf:
  `Etale.constantSheafCompUpperStarIso` (the module-valued comparison).
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`,
  through `MapIsSeparated` in AlgebraicSpaceMorphismProperties.
- Sheaf.CategoryTheory.RingedSiteModules: `ringedSiteModules`. The six-functor
  family uses the project's accepted constant-coefficient `Sheaf ... (ModuleCat ...)`
  encoding, as prescribed in STATE, not a copied module category.
- Sheaf.AlgebraicGeometry.RegularGroupSpace: `CommutativeSpaceGroup`,
  `groupSpaceProjection`; AlgebraicSpaceMorphismProperties: `MapIsLocally`,
  `MapIsSeparated`, `MapIsLocallyOfFinitePresentation`; ProperCurveModuli:
  `MapIsQuasiCompact`.
- Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres:
  `HasSemiabelianGeometricFibres`; Mathlib `Grp`, `IsCommMonObj`, `yonedaGrpObj`,
  `Over.map` and `Over.pullback` implement the fibre models and their group laws.
- Mathlib.Algebra.Module.Torsion.Basic: `AddSubgroup.torsionBy`,
  `AddSubgroup.torsionBy.zmodModule`; Mathlib.Algebra.Module.ZMod:
  `AddMonoidHom.toZModLinearMap`.

Recorded proof imports are retained for components, normality of etale charts,
normal constant open units and constant pullback comparison. No import cycle found.
Their declarations and docstrings were read; the theorem docstring carries all six
proof steps of the node, including componentwise gluing for infinitely many components.

Edge checks: S empty forces V empty and the unique zero sheaves, with no `Nonempty`
assumption. S may have infinitely many disjoint components. Rank zero and n=1 give
the zero label module; the existence of α correctly forces the restricted torsion
sheaf to be zero. A toric boundary may have smaller torsion rank, so β is only a
monomorphism. The open may equal all of S. No primality or rank=2g hypothesis was
added. Fields used to test fibres lie in the scheme universe; coefficients are
uniformly lifted to u+1, as required by the published six-functor API.

Searches: msearch LeanFinder "An etale torsion frame over a dense open of a normal
base extends uniquely as an injection into a constant sheaf" returned affine
section and normalization lemmas, no match. Loogle `"torsion", "sheaf"` returned
zero hits. Mathlib grep `semiabelian|semiAbelian|torsionFrame` returned zero hits.
LeanSearch "The etale sheaf of n torsion sections of a commutative group algebraic
space, and semiabelian geometric fibres" found `AddSubgroup.torsionBy` and the
small etale site, reused. A second LeanFinder query for semiabelian algebraic-space
geometric fibres and torsion returned etale morphism and ring lemmas, no match.
Repository rg found RegularGroupSpace and SemiabelianGeometricFibres, reused;
there was no space torsion sheaf or frame-extension declaration. The prescribed
upstream item-ID grep returned no match. DAG definition searches and
blueprint_refs.py searches for semiabelian and torsion frame supplied no missing
construction node. Exact search output is recorded in the new node's mathlib_searches.

Validation: scompile.py compiled both modules separately in dependency order against
the published live server build, with no errors or unexpected warnings.

## New nodes

`def-sfb-space-group-torsion` provides the missing actual torsion module presheaf,
its named sheaf-condition obligation, its sheaf, the constant labels and canonical
restriction and group-isomorphism transport maps. It also packages group-space
geometric semiabelian fibres by the already recorded scheme-fibre predicate and
abelian-open representability. Source: Deligne Sections 1.1 and 3.5.2. Searches above
show why this is absent while its constituent notions already exist; those are
imported and cited, with no private copies. The item's statement dependencies gain
only this new definition node. Its definition statement explicitly includes the
sheaf-condition assertion belonging to the construction obligation.

## Second reading by Q82

This replaces the worker's own pass. It was written by the maintainer's independent
reader, with the node, Deligne Lemma 3.5.2 (as summarised in the node record) and both
delivered modules open. No Lean file was changed.

Node clauses and the Lean that renders them:

- S normal and locally Noetherian: `[IsLocallyNoetherian S]` (the pqf-def-locnoeth
  record), plus `hnormal`, which says every stalk is a domain and integrally closed.
  S is not assumed integral or nonempty. Exact.
- j a dense open immersion: `[IsOpenImmersion j]` and `DenseRange j.base`. Exact.
- N separated, smooth, finitely presented: `hsmooth`, `hseparated` and `hfp`. These are
  the conjuncts of the landed `IsSmoothIntegralGroupSpace` (def-sfb-smooth-integral-group-space)
  without the integral-fibre conjunct. Finite presentation is local finite presentation
  plus quasi-compactness of p and of its diagonal; separatedness is a diagonal
  representable by closed immersions. Exact, and nothing is stronger than the node.
- Commutative group algebraic space: `H : CommutativeSpaceGroup N`, the given natural group law.
- Fibres are extensions of abelian varieties by tori: `HasSemiabelianSpaceFibres H`.
  For every algebraically closed K in the scheme universe and every s : Spec K → S,
  there is a group-functor isomorphism (not just a space isomorphism) with a commutative
  group scheme over K that satisfies the landed `HasSemiabelianGeometricFibres`.
  Asking for a scheme model is not stronger than the node: a group algebraic space
  locally of finite type over a field is a scheme. Connectedness and smoothness of the
  extension are automatic.
- N_V an abelian scheme: `IsAbelianOn H j`. N restricted along `Over.map j` is
  group-isomorphic to the functor of points of a proper, smooth group scheme over V
  with connected geometric fibres. Exact.
- n ≥ 1, n invertible, r ≥ 0: `hn`, `hinvertible` (n is a unit in every stalk) and
  `r : ℕ`. Exact.
- N[n]: `spaceTorsionSheaf H n`. Its sections are `AddSubgroup.torsionBy (N(T)) n`,
  with Mathlib's ZMod-module structure lifted through `ULift.ringEquiv`. Restriction
  maps are the given group maps. The sheaf condition is a named sorried theorem
  carried by the new definition node (H5 is respected). The claim is true: an étale
  cover is an fppf cover and n·x = 0 is a local condition.
- Injectivity of N[n] → j_*j^{-1}N[n]: `Mono` of the unit of the recorded
  `Etale.upperStarLowerStarAdjunction` at N[n]. A monomorphism of module sheaves is
  sectionwise injective. Exact.
- α : N_V[n] ≅ (Z/n)^r_V: an isomorphism from `localizationRestriction j` of N[n]
  (the site restriction, whose sections are N(T → V → S)[n] = N_V[n](T)) to the
  Mathlib constant sheaf `torsionLabels V n r`. The restriction is canonically
  isomorphic to j^{-1} by the published `upperStarIsoLocalizationRestriction`. Exact.
- A unique monomorphism ᾱ restricting to α: `∃ β, Mono β ∧ (restriction of β) ≫
  torsionLabelsRestriction = α.hom ∧ ∀ γ, (same equation) → γ = β`. The label
  comparison is canonical: the published `upperStarIsoLocalizationRestriction` and
  `constantSheafCompUpperStarIso`, which is `leftAdjointUniq` of the constant-sheaf
  adjunctions. Uniqueness is stated among all module-sheaf maps. Node proof step 6
  proves exactly this form, and it implies the node's "unique monomorphism".
  Accepted.
- Naturality under base isomorphisms and group isomorphisms carrying frame to frame,
  with the identity on labels: the last conjunct. `spaceTorsionTransport` applies the
  given group isomorphism `e` to actual torsion elements. If the transported β′ has
  open frame α, it equals β. The labels are compared by the canonical
  `torsionLabelsRestriction h.hom`. This is node step 6 (naturality from uniqueness),
  with no arbitrary label automorphism.

Edge cases: S empty (then V is empty and all sheaves are zero; there is no
`Nonempty` hypothesis); infinitely many components; V = S; n = 1 or r = 0 (the
labels are zero, so α forces N_V[n] = 0); toric boundary torsion of smaller rank
(β is only a monomorphism); universes (fields in Type u, coefficients lifted to u+1
as the six-functor API requires). Each case is covered.

Records: the item node changes only in `lean` and in `stmt_deps`, which gains just
the new definition node. Both `lean.statement` fields are verbatim slices of their
files. No line is over 100 characters. Docstrings carry the source place and the
blueprint id, and the theorem docstring carries all six proof steps. Proof-dependency
modules are plain `import`s, as brief-stage2 rule 7 requires.

Searches: I grepped the live lean/Sheaf and WeilConjectures trees for
IsAbelianScheme, AbelianScheme, spaceTorsion, torsionLabels and torsionBy, and found
no étale torsion sheaf of a group space. The Poincaré `IsAbelianFamily` is an
algebraic-space family predicate without scheme representability, so it is not the
node's "abelian scheme". `def-weil-pbc-torsion-etale-sheaf` is the kernel of n on an
abelian sheaf and does not build N[n] from N. The new node is not a duplicate.

Mismatches found: none in the Lean. The only change is this section, which replaces
the worker's self-audit (H11).
