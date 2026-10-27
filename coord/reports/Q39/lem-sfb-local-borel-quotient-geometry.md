## Worker report

The delivery states `AlgebraicGeometry.local_borel_quotient_geometry` in
`Sheaf.AlgebraicGeometry.GroupScheme.LocalBorelQuotientGeometry`, with one `sorry`.
The helper `LocalBorelGeometry` expands the geometric conclusions for specified
maps, and the new definition node supplies the full-coaction relative weight
predicate. All definitions contain actual data; there are no other postponed
proofs. The item's natural-language statement is unchanged.

Hypotheses, matched individually:

- The ring is `A : Type u` with `[CommRing A] [IsNoetherianRing A]
  [IsLocalRing A]`. In this Mathlib, `IsLocalRing` implies `Nontrivial A`, so
  this includes the explicit nonzero hypothesis without a redundant instance.
- The base is literally `Spec (.of A)`. `H T B : Grp (Over (Spec (.of A)))`
  uses the dependency's group-object diagrams over this base, not a group of
  rational points.
- Smoothness of H, T, B is `[Smooth ...X.hom]` individually.
  `[IsAffineHom H.X.hom]` and `[LocallyOfFinitePresentation H.X.hom]` render
  affine finite presentation: an affine morphism is already quasi-compact and
  quasi-separated, so locally finite presentation is finite presentation here.
- `j : T ⟶ B` and `iB : B ⟶ H`, with both underlying maps closed immersions,
  render the two smooth closed subgroup inclusions. The composite is the
  specified inclusion of T in H.
- `r : ℕ` and `e : T ≅ RingGroupSchemes.splitTorus A r` render the given split
  torus, including r = 0. This is the existing product of actual Laurent-Hopf
  multiplicative groups; the coordinate is not an unspecified torus model.
- `hred` applies `ReductiveTorusCentralizer.IsReductive` to every pullback
  to an algebraically closed A-field. Its definition includes connectedness,
  smoothness, affineness, finite type and triviality of every smooth connected
  normal unipotent subgroup after algebraic closure. Its unipotence is a
  faithful finite-dimensional matrix representation, on all geometric points.
- `hmax` says that the pullback of `j ≫ iB` is a maximal torus on every
  geometric fibre, using the existing subgroup-inclusion maximality predicate.
- `hB` uses the existing `IsBorelGroupScheme` on every geometric fibre of iB.
  That predicate is exactly smooth connected solvable closed subgroup maximality;
  solvability is the scheme-theoretic derived-series notion.

Conclusions, matched individually:

- Existential `U`, `iU`, `p` are group schemes and homomorphisms over the base.
  `LocalBorelGeometry` asserts `Smooth U.X.hom`, closedness of iU, and normality
  of its image on every test scheme W. This is relative schematic normality,
  including nonreduced test rings.
- For every geometric point `s : Spec (.of F) ⟶ S`, the U fibre is connected
  and unipotent; every smooth connected normal unipotent closed subgroup N
  of the B fibre factors through that U fibre. This is precisely that the
  U fibre is the largest such subgroup, hence its unipotent radical.
- `j ≫ p = 𝟙 T` is identity on T. The `IsPullback` square with iU, p and
  the unit of T is the scheme-theoretic kernel statement. The multiplication
  map `T.X ⊗ U.X ⟶ B.X`, literally the product of the two inclusions, is
  `IsIso`. Together with normality and the given subgroup laws this identifies
  the group law with the conjugation semidirect product T ⋉ U; no separate
  arbitrary group law or arbitrary map replaces multiplication.
- `Q : Over ...` with `Smooth Q.hom ∧ IsProper Q.hom` is the smooth proper
  relative flag scheme. Its map π is flat, surjective, quasi-compact and locally
  finitely presented, as separately asserted in `LocalBorelGeometry`.
- The `IsPullback` square has top/left maps `fst` and
  `fst * (snd ≫ iB.hom.hom)`: on test points these are g and gb. This says the
  canonical `(g,b) ↦ (g,gb)` is the specified kernel-pair isomorphism
  H × B ≅ H ×_Q H, rather than just some unspecified isomorphism.
- Fppf sheafification/representation is rendered by this kernel-pair condition
  and the following local-lifting clause for every W and x : W ⟶ Q. The latter
  uses `Scheme.fppfPrecoverage`, whose definition is exactly jointly surjective
  families of flat locally finitely presented morphisms. Representables are
  sheaves for this subcanonical topology. Thus the map from pointwise cosets
  to the represented sheaf is locally surjective and has precisely those
  coset equivalence classes: it induces an isomorphism on sheafification.
  W is any test scheme, not necessarily affine.
- For every scheme S' and every map f to Spec A the theorem asserts
  `LocalBorelGeometry` on the literal pullbacks of j, iB, iU, p, Q and π.
  Thus the radical, kernel, retraction, multiplication, quotient and torsor
  on S' are those pulled-back maps. They are characterized by the same radical
  and quotient conditions. This is formation under arbitrary base change,
  including nonaffine and empty S'; successive pullbacks have their usual
  canonical identification from the recorded base-change construction.
- The roots are the actual-character sets `rootsOver (j ≫ iB) A` and
  `rootsOver j A`. The first root clause is equality with positive roots or
  their inverse characters; the second excludes their intersection. Character
  inversion is negation in X*(T), so these are exactly Φ = Φ⁺ ⊔ (-Φ⁺).
  The given splitting e identifies this character group with Z^r; using actual
  characters avoids an additional arbitrary lattice basis in the statement.
- For each algebraically closed A-field F, `Function.Bijective` on
  `(Over.pullback (Spec.map ...)).mapGrp.map` is the restriction identification
  of actual character groups. It is the canonical group homomorphism, so
  bijectivity is equivalently the asserted group isomorphism. The two following
  iff clauses equate the occurrence sets on A and F for H and B separately.
  With that bijection they say restriction carries Φ and Φ⁺ onto precisely
  the nonzero Lie weights of the corresponding geometric fibres.
- `HasWeightOver` uses tangent vectors as nonidentity dual-number points reducing
  to 1 and tests the conjugation eigenvector equation after EVERY algebra
  extension. The character value multiplies epsilon itself. Thus these are
  weights for the full coaction, not weights of A-points or differentiated
  characters; Lie(B) is the actual dual-number tangent module.
- The last implication, `IsIso (j ≫ iB) → ...`, is the coordinate-free condition
  H = T as a subgroup. It concludes U is the trivial group and Q is the terminal
  S-scheme, equivalently U = 1 and Q = S. The formulas with p and π are already
  supplied by the retraction and quotient clauses.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`,
  bundled homomorphisms and their induced Hom groups. GrpObj is base-independent;
  the field in the informal introductory group-scheme node imposes no restriction
  on its recorded declaration.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `...Morphisms.Affine`: `IsAffineHom`;
  `...Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its convention is
  `Over.pullback` on schemes/maps, geometric fibres by Spec of an algebraically
  closed residue extension; the six recorded signatures/docstrings were read.
  Module base change is not confused with group/scheme base change.
- The existing definition nodes `def-sfb-split-torus-over-ring`,
  `def-sfb-reductive-torus-centralizer-terminology`, and
  `def-sfb-borel-subgroup-scheme` are added to stmt_deps, and their recorded
  declarations are imported and used, without duplicating their definitions.
- Proof imports include all currently stated proof dependencies: the finite-type
  and finite-presentation Mathlib algebra facts, finite projective prime local
  freeness, Borel opposite-root dichotomy, reductive Borel-pair structure,
  schematic Borel normalizer, smooth-to-flat/lfp and Noetherian geometry.
  The other proof dependencies have no statement modules yet and are named in
  the complete twelve-step proof docstring; none is needed as an extra
  hypothesis to this statement.

Edge cases read before writing and checked again: r = 0; H = T; empty root set;
nonreduced A; positive and mixed residue characteristic; nonhenselian local A;
base changes to a nonaffine S', the empty scheme and the zero algebra. No field,
reducedness, characteristic, semisimplicity, or henselianity assumption is added.
The root predicate is empty over the zero ring because there is no nonidentity
point of an affine group over that base. For every algebra tower there is a
unique map of dual numbers fixing epsilon and extending the constant inclusion;
therefore quantifying over maps with these equations in HasWeightOver is not
vacuous and is exactly the canonical extension. The same universe u is used for
A and its test algebras/fields, not an independent potentially smaller universe.

Searches made (full service results are also carried by the new definition node):

- LeanFinder: "A reductive group scheme over a local ring with split maximal
  torus and Borel has a unipotent radical semidirect product and smooth proper
  fppf quotient" returned eight Lie-algebra semisimplicity and unrelated
  category-theory hits, no group-scheme statement.
- Loogle: "AlgebraicGeometry.GroupScheme, AlgebraicGeometry.Scheme, IsReductive"
  returned no hits (unknown identifier AlgebraicGeometry.GroupScheme).
- msearch grep: "IsReductive|IsBorel|relativeWeight|RelativeWeight|weightSpace"
  in Mathlib AlgebraicGeometry returned no matches.
- LeanSearch and LeanFinder: "Relative adjoint character weight of group scheme
  defined by dual number points over all test algebras" each returned eight
  unrelated dual-number, root-system or Lie-algebra-character declarations.
- msearch grep: "HasWeightOver|RelativeAdjointWeights|adjoint.*weight|weight.*dual"
  returned seven unrelated number-theory/Lie-weight/root-system hits.
- rg in WeilConjectures and Sheaf found field-only tangent character weights,
  field-only character-value helpers, the existing Lie.Ring dual-number point
  machinery over a ring, and the existing relative torus-module coaction
  weightSpace. None supplies the missing differentiated conjugation coaction or
  its all-algebras eigenvector predicate over a ring. The new predicate uses
  the actual existing group points directly, rather than postulating that coaction.
- rg on the item id in WeilConjectures found no declaration. rg on the new
  predicate/name in both roots found no match. DAG grep found no definition
  of relative adjoint weights; `blueprint_refs.py search 'adjoint weights'`
  returned zero nodes. The distinct field-only weight node was read.

Source read: the current blueprint unit under literature/blueprint/latest and
Conrad's primary-author PDF at the URL in the node, specifically Proposition
5.2.3 and Corollaries 5.2.5 and 5.2.8, printed pp.152--156, plus the surrounding
split-root and Borel discussion. No statement fault or dispute was found.

Validation: scompile.py compiled each delivered file separately, in dependency
order, in both sandbox and library-module modes. The first compile caught a
redundant Nontrivial instance binder; after removing it, both modules compiled
without errors or warnings. No local or global Lean build was run.

## Second reading by Q39

I reopened both node files and both Lean files for a separate clause-by-clause
pass. No second agent was started, as the dispatcher's brief prohibits that;
the delivery receives the maintainer's independent review. The second pass
checked the equations defining the actual kernel-pair map, the order T × U
in semidirect multiplication, the quantification over all geometric fibres and
all algebra extensions, the restriction-map codomain, and the two distinct
root equalities for H and B. It verified that the base-change conclusion uses
the literal images of the specified maps, rather than unrelated existential
maps on S'. It also checked the largest-subgroup condition in the radical
clause. The only change from checking was removal of the redundant explicit
Nontrivial A binder; nonzeroness is still an assumption through IsLocalRing.
The item record is the original JSON with only lean and added definition
stmt_deps changed; no statement correction is made.

## New nodes

`def-sfb-relative-adjoint-weights` defines the actual-character occurrence
predicate on relative identity tangent vectors, and the nonzero adjoint weight
set. Its source is Conrad, Section 4 opening, p.107 and Proposition 5.2.3,
pp.152--153. The recorded LeanSearch, LeanFinder, Mathlib grep, both project-root
searches and DAG/blueprint searches above found no existing relative notion.
The existing `TorusCharacterTangent.weightSpace` is explicitly field-only and
tests field-valued points; the existing module-coaction weightSpace requires
an already constructed linear coaction, which is not supplied for relative
conjugation. Here the canonical eigenvector equation is defined directly by
conjugation and scalar substitution on dual-number points after every algebra
extension. The scalar is the actual Laurent coordinate evaluated on a character.
This supplies precisely the missing notion without any choice or sorry data.
