## Worker report

The module `Sheaf.AlgebraicGeometry.TorusIntegralCosetSpecialization` states
`AlgebraicGeometry.torus_integral_coset_specialization`, with `sorry` as its entire proof.
The two helper definitions give the actual contravariant Spec restriction map and the
representative formulation of coset surjectivity. Their data and predicates are written in full.
The existing landed module `Sheaf.AlgebraicGeometry.NeronLftModel` supplies the Néron
mapping-property predicate, with its explicit generic group and group isomorphism. No live source file was modified, and no Git command was run by
this worker in the shared read clone.

Source checked: BLR, *Néron Models*, 10.1 Definition 1 and Proposition 7, printed
pp.289, 292–293 (PDF pp.295, 298–299), and 3.6 Definition 1, printed p.78 (PDF p.84),
in the [author-hosted scan](https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf).
In particular 3.6 Definition 1 explicitly defines separability of the residue extension by
reducedness after field extension; it does not mean algebraicity. Proposition 7's initial
Hom(H,G_m)=0 assumption is used to construct the integral extension B from line bundles,
which is already supplied in this node. Its coset calculation uses the supplied B, not that
extra assumption. The original item statement, proof, sources, status and proof dependencies
are unchanged; its statement dependencies gain the existing ring-torus node and the landed
Néron definition node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- D is a strictly henselian DVR: `CommRing D`, `IsDomain D`,
  `IsDiscreteValuationRing D`, `IsStrictlyHenselianLocalRing D`.
- F is its fraction field: `Field F`, `Algebra D F`, `IsFractionRing D F`.
  The base scheme throughout is `Spec (.of D)`.
- M, Q and B are actual group schemes over this base: `Grp (Over (Spec (.of D)))`.
  Their multiplication, identity and inverse are the existing group-object structure,
  not arbitrary operations. `IsCommMonObj` imposes commutativity on each.
- M is smooth and separated: the `Smooth M.X.hom` and `IsSeparated M.X.hom` binders.
  `IsSeparated` is precisely the closed-diagonal predicate recorded by the node's
  definition of separatedness. Smoothness implies local finite type; quasi-compactness
  of M is deliberately absent.
- M is Néron lft: `hM : IsNeronLftModel M
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D F)))).mapGrp.obj M)
  (Iso.refl _)`. This uses the landed Q92 definition with the actual generic group
  and its identity isomorphism. Unfolding gives smoothness, the closed-diagonal
  separatedness condition, and bijectivity of generic restriction on Hom for EVERY
  smooth object X of the slice. No finite-type restriction on X is present.
- The generic group H is represented by the actual generic fibre
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D F)))).obj M.X`.
  This is a choice of notation for H via its supplied identification, not a restriction
  on H or a replacement group. Its group structure is induced by `mapGrp`, its
  smoothness and separatedness are inherited from M, `hH` gives geometric connectedness,
  and `hHft` gives quasi-compactness. Together with smoothness this is finite type.
- Q is the finite-type open subgroup: `j : Q ⟶ M`,
  `IsOpenImmersion j.hom.hom.left`, `LocallyOfFiniteType Q.X.hom`,
  `QuasiCompact Q.X.hom`. Since j is a group morphism, it is a subgroup inclusion.
- Fibrewise identity components: `hQ` tests every algebraically closed field Ω and
  every Ω-valued base point s, and equates the range of the base-changed inclusion with
  `connectedComponent` of the image of the identity section. These are the actual
  geometric fibres, including the generic fibre. The open immersion supplies the
  correct open-subscheme structure; this is not merely a chosen connected subgroup.
- Q_F=H: `hQF` says the canonical generic-fibre inclusion is an isomorphism. Thus
  the generic identifications are compatible with j, not independently chosen maps.
- B is smooth, separated and finite type with geometrically connected fibres:
  the five class binders `Smooth`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `GeometricallyConnected` on its structure morphism.
- The split torus has any rank `r : ℕ`, including zero, and is the existing
  `RingGroupSchemes.splitTorus D r`; its Laurent-coordinate Hopf group law is reused.
- The arrows `i` and `q` are morphisms in `Grp`, so preserve the group operations.
  `hker : IsPullback i.hom.hom (toUnit ...) q.hom.hom η[Q.X]` is exactly the
  scheme-theoretic kernel square in the slice. Since Q's identity is a section and
  hence a monomorphism, this also gives the injection of the kernel.
- Exactness on the right: `hepi : Presheaf.IsLocallySurjective
  (Scheme.fppfTopology.over (Spec (.of D))) (yoneda.map q.hom.hom)`.
  This tests actual sections on the big fppf site, not just field-valued points.
- The group G is B_F. By the pullback universal property its F-points are exactly
  `(algSpec (.of D)).obj (op (CommAlgCat.of D F)) ⟶ B.X`. Using this representation
  also identifies its L-points and integral sections with the corresponding Hom sets.
- Integral subgroup restriction is precomposition by the canonical Spec maps, realized
  by `algSpec.map`. D-sections use the unique map `toUnit` to the slice's terminal object.
  Separatedness and dominance of the generic point make these inclusions injective;
  no extra injectivity hypothesis on the point maps is imposed.
- (a), the first conjunct: L is any field and V any `ValuationSubring L`.
  `Algebra D V`, `IsScalarTower D V L`, `IsLocalHom (algebraMap D V)` and
  `Function.Injective (algebraMap D V)` give exactly the local injective valuation
  extension. Every abstract valuation ring embeds in its own fraction field this way;
  `ValuationSubring.isFractionRing` identifies L as its fraction field.
  A compatible `f : F →ₐ[D] L` is the unique induced fraction-field embedding.
  For each F-point a, the existential b and displayed equality assert that a_L is the
  restriction of an integral V-point. The conclusion is existence of a D-section b
  whose generic restriction is a, precisely a in B(D).
- (b), the second conjunct: A is any DVR, with a local injective D-algebra structure.
  The existential π asserts both `maximalIdeal D = Ideal.span {π}` and
  `maximalIdeal A = Ideal.span {algebraMap D A π}`. A DVR is not a field, so these
  equations force π nonzero and are precisely the common-uniformizer condition.
  `Algebra.IsGeometricallyReduced (ResidueField D) (ResidueField A)` uses the canonical
  residue algebra induced by that LOCAL algebra map. Over fields this is the source's
  general separability condition, equivalent to reducedness after every field extension.
  It includes separably generated transcendental extensions, with no algebraicity binder.
  L is any fraction field of A. Its D-algebra and the F-algebra hom f are compatible.
  `IntegralCosetSurjective D F A L B f` means that every a' in G(L) has an expression
  `a_L * b_L`, with a in G(F) and b in B(A). This is equivalent to surjectivity of
  G(F)/B(D) → G(L)/B(A): choose a representative of any target coset in one direction;
  in the other direction equality of cosets says exactly that their ratio is integral.
  The quotient map is well defined since D-sections restrict to A-sections.
- The final conjunct is the stated 'in particular': X is ANY smooth D-scheme and x ANY
  point. A is a DVR with a local injective D-map and `e : A ≃+* O_(X,x)`.
  The displayed Spec equality says this is an identification as D-algebras with the
  canonical local-ring map, rather than an arbitrary ring isomorphism. Contravariance
  requires `Spec.map e.symm.toRingHom` here. The conclusion is the SAME
  `IntegralCosetSurjective`, without demanding the common uniformizer or residue
  separability as extra hypotheses. Those are consequences, as the node requires.
- No perfectness, excellence, completeness, finite residue field, or positive-rank
  condition occurs. One explicit universe u is shared by rings and test schemes;
  test schemes/fields are not quantified in an independently smaller universe.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.NeronLftModel`: the landed Q92
  `AlgebraicGeometry.IsNeronLftModel N V e`, restored at commit 6e0cf090491.
  Its complete signature and docstring were read on repair. We apply it to N=M,
  V=the canonical base change of M, and e=`Iso.refl _`.

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` (local
  principal ideal domain with nonzero maximal ideal), and the proof dependency
  `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`, defined by that
  predicate on the diagonal, and proof dependency `ext_of_isDominant_of_isSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the node's base-change
  convention is the actual `Limits.pullback` / `Over.pullback`. Its full recorded
  bundle was read; the module-only base-change helper is not a substitute for X_F.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, `connectedComponent`.
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology` and the definition of its
  fppf covering families; `Mathlib.CategoryTheory.Sites.Over`: `.over`;
  `Mathlib.CategoryTheory.Sites.LocallySurjective`: `Presheaf.IsLocallySurjective`.
- The newly cited existing `def-sfb-split-torus-over-ring`:
  `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`,
  `AlgebraicGeometry.RingGroupSchemes.splitTorus` and `multiplicative`.
- Other existing interfaces used directly: `Grp`, `IsCommMonObj`, `algSpec`,
  `ValuationSubring`, `Algebra.IsGeometricallyReduced`, `Scheme.fromSpecStalk`,
  and `IsLocalRing.ResidueField.algebra`. No private version of any is introduced.
- The remaining four non-Mathlib proof prerequisites have no Lean records at reading
  time: local-split-torus-extension-points, neron-strict-local-descent-base-change,
  strict-local-group-component-translates, essentially-smooth-dvr-index-one. Their
  statements and proof plans were read and their use is recorded in the theorem's
  six-step proof docstring. No absent proof module was imported and no proof was
  assumed as an extra hypothesis of this statement.

Edge cases checked before and after writing: r=0 (trivial torus, empty coordinate tuple),
the trivial groups, A=D, V=D realized inside F, valuation rings of higher rank,
imperfect residue field, non-complete and non-excellent DVRs, transcendental separable
residue extension such as D[t]_(π), and non-quasi-compact M. A ramified extension with
e>1 fails the explicit common-uniformizer hypothesis. Empty X is permitted by the Néron
predicate; the final pointwise assertion then has no x. A, D and V cannot be zero rings
because of the domain/field assumptions already present in the source.

Searches made:

- `msearch.py leanfinder`: 'Neron model split torus extension integral point cosets under
  ramification index one valuation ring extension'; 8 hits, Selmer groups and arithmetic
  valuation statements only, no scheme-theoretic integral coset theorem.
- `msearch.py loogle`: '"IsDiscreteValuationRing", "Units"'; 2 hits, the uniformizer
  decomposition and valuation kernel, neither the desired statement.
- `msearch.py grep`: `Neron|Néron|integralCoset|splitTorus`; no Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`: Neron/neron, integral cosets,
  split tori, commutative group objects and identity components. The ring split torus
  was found and reused; field-only split tori were not redeclared or misapplied to D.
- `rg -n lem-sfb-torus-integral-coset-specialization lean/WeilConjectures`: no hits.
- Original pre-return Néron-definition searches (superseded by the landed Q92
  definition, now imported directly): `msearch.py leansearch` for bijective generic restriction
  of smooth test schemes; 8 hits for smoothness and valuative criteria, no Néron predicate.
  `msearch.py leanfinder` for the Néron lft mapping property; 8 smoothness hits only.
  `msearch.py grep` with `IsNeron|NeronLft|Néron|Neron.*[Mm]odel`: no Mathlib hits.
  The same `rg` on both source Lean trees and definition-node files gave no matches.
  `tools/blueprint_refs.py search Néron` returned 0 blueprint nodes. The ancestor command
  returned no blueprint ancestor, agreeing with the item's inherited null from.node.

The current blueprint direct-image proof (3) was read from
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`: it uses compactification and the
proper/open direct-image results. This delivery only states the already accepted
lower BLR coset prerequisite and does not change that unit or its route.
The name search also checked `dag/lean_names_upstream.json` and found no collision.

Validation for this repair: only `TorusIntegralCosetSpecialization.lean` is delivered.
It is compiled with `scompile.py` against the live landed Néron definition, followed by
the delivery dry run and delivery wrapper. Exactly one sorry remains, the entire proof
of the item theorem. The helpers and all clauses other than hM are unchanged from the
independently reviewed returned head 7ab2a0cec5f5. No mathematical statement correction
or new node is needed.

## Repair of return A4/H4/H12

The return identified a concurrent landing: Q92's reviewed definition at
`def-sfb-neron-lft-model` and `NeronLftModel.lean`, restored on sheaf-dag in 6e0cf090491,
uses a group model N, a generic group V and a specified generic isomorphism e.
Removed our sandbox copies of that node and module and removed the New nodes section.
The landed node stays in the item's statement dependencies. Replaced hM with exactly
`IsNeronLftModel M
((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D F)))).mapGrp.obj M)
(Iso.refl _)`, so it imports and uses the reviewed interface without overwriting it.
Regenerated `lean.statement` verbatim and refreshed the item's unchanged metadata from
the current sheaf-dag read clone. The prescribed `deliver2.py` wrapper fetches sheaf-dag
and constructs the repaired delivery on its current tip, performing the authorized rebase
without direct Git mutations in the shared repository. The repair packet contains just
the item module, item node and report; neither landed dependency file is delivered.

## Second reading by Q81

I reopened the original node, the completed item module and the landed Q92 dependency and checked the correspondence
above after compilation. This is the worker's second pass, not a claim to an independent
review; the dispatcher brief forbids starting other agents and assigns independent review
to the maintainer. I specifically checked every conjunct: the valuation conclusion is
existence of a D-section for the SAME point, the ramification-one conclusion is surjectivity
via coset representatives (not injectivity), and the final smooth-local-ring clause has no
extra separability hypothesis. The earlier wrong direction of Spec of the stalk isomorphism
was corrected to e.symm. The base-changed identity point now names `mapGrp.obj M` explicitly,
so it has the actual induced group law. The hQ range equation gives the full identity
component, not just connectedness of Q. Residue separability uses geometric reducedness
rather than algebraic separability, preserving the D[t]_(π) case. The landed Néron predicate
quantifies over all smooth X; hM now uses its actual generic group with `Iso.refl _`.
No missing theorem or Néron existence result is smuggled in as a binder. The return
A4/H4/H12 is addressed by reusing Q92 rather than delivering a competing definition. No statement or proof-plan change was needed.
