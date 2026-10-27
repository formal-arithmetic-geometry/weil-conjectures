## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralNodalPicardNormalizationAction` states
`AlgebraicGeometry.integral_nodal_picard_normalization_action`, with its entire proof
postponed by `sorry`. All five supporting definitions have real data. The natural-language
statement and reviewed proof are unchanged. The existing definition node
`def-sc-picard-group` was added to statement dependencies because the statement explicitly
uses invertible-sheaf classes and their group law.

Source read: Deligne--Mumford, *The irreducibility of the space of curves of given genus*,
Lemma 1.15 proof, printed p.85, primary PDF at
https://www.numdam.org/item/PMIHES_1969__36__75_0.pdf (PDF page 11). In particular the proof
uses a distinct morphism for each singular point with an ordering of its two inverse images.
Also read local Stacks `curves.tex`, `lemma-glue-points` (Tag 0C1M), lines 3106 onward,
including the unit sequence, surjectivity and the injectivity condition. Read the latest
blueprint direct-images proof under `literature/blueprint/latest/`; this is an auxiliary
node and does not change the unit's statement or route.

Hypotheses and clauses, individually:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Integral curve over that field: `(Y : Scheme.{u}) [IsIntegral Y]` and
  `(f : Y ⟶ Spec (.of k))`. Projectivity is `[IsHProjective f]`, the recorded finite
  projective-space embedding convention. The recorded nodal condition is
  `(hnodal : HasNodalGeometricFibres f)`, with its required
  `[LocallyOfFinitePresentation f]`. On an algebraically closed base this says exactly
  nonempty connected dimension one and only nodes; these conditions persist after
  algebraically closed extension. Finite presentation is already implied by projectivity
  over a field and is explicit here to use that recorded interface, not an added restriction.
- Normalization: the canonical `Y.normalization` and `Y.fromNormalization` from the recorded
  dependency, not an arbitrary finite map or replacement scheme. Its structure map is
  `Y.fromNormalization ≫ f`.
- Smooth projective connected curve: first four conjuncts are `Smooth`, `IsHProjective`,
  `ConnectedSpace`, and `topologicalKrullDim ... = 1` for this canonical normalization.
- Ordinary degree zero: `nodalPicardDegreeZero k g M` is exactly
  `Scheme.Modules.degree k` of the existing skeleton representative of `M`, with the
  structure morphism supplied by `g`. That degree is the recorded Euler-characteristic
  difference; it is invariant under the choice of representative.
- Pic^0(Y): the same predicate applied to `Scheme.Pic.map Y.fromNormalization L`.
  No multidegree condition or arithmetic-genus condition is imposed on Y.
- Surjectivity of normalization pullback on Pic^0: every normalized class M with degree
  zero has a class L of normalized degree zero with `Scheme.Pic.map ... L = M`.
- The two inverse images of each node: the next conjunct quantifies over rational nodes q,
  and gives `r : NodalOrderedBranch k f` above q, with every rational inverse image equal
  to `r.minus` or `r.plus`. The structure includes distinctness, both composition equations,
  the structure-map equation for q, and nonsmoothness. Over the stated algebraically closed
  field, nodes and their branches are rational, so this covers all node orderings.
- Gluing homomorphism: the existential j assigns a genuine group homomorphism
  `kˣ →* Y.Pic` to every ordered branch. Its image has normalized degree zero, which
  expresses precisely a homomorphism into the specified subset Pic^0(Y).
- The maps really are the specified scalar gluings: `IsNodalScalarGluing r z (j r z)`
  requires a single trivialization of the normalized line, simultaneously for all nodes.
  At s its two fibre coordinates differ by `nodalBranchScalar r s z`: z at r,
  z inverse at the reverse ordering, and 1 elsewhere. The equality uses canonical
  `pullbackComp`, `pullbackCongr`, `pullbackObjUnitIso` and multiplication by the image
  of the scalar under `Scheme.ΓSpecIso.inv.hom`. This specifies gluing of the actual line,
  not just an unconstrained map into the kernel of Picard pullback.
- Each homomorphism is injective: `∀ r, Function.Injective (j r)`.
- All homomorphisms are pairwise distinct, including reverse orderings:
  `Function.Injective j`. Proof irrelevance in the branch structure prevents different
  proofs of the same ordering from creating spurious indices.
- Every k-automorphism: `(b : Y ≅ Y)` with `b.hom ≫ f = f`.
- Unique lift: an isomorphism β of the canonical normalization with
  `β.hom ≫ Y.fromNormalization = Y.fromNormalization ≫ b.hom`, and every isomorphism γ
  satisfying that equation equals β. Its k-linearity follows from this square and the
  k-linearity of b, so no action is left unspecified.
- Pullback permutes the gluings: for r there is s whose node and two branches are the
  inverse images under b and β, and `Scheme.Pic.map b.hom (j r z) = j s z` for every z.
  This is the contravariant formula of proof step 8, with the ordered pair retained.
- Actions on both degree-zero subsets: two explicit iff clauses say b and β preserve
  the respective degree-zero predicates. Thus the restrictions of the canonical Picard
  pullbacks are well defined without choosing auxiliary group structures.
- Picard-triviality hypothesis: every L whose normalization pullback has degree zero
  satisfies `Scheme.Pic.map b.hom L = L`.
- First consequence: every ordinary degree-zero normalized class M satisfies
  `Scheme.Pic.map β.hom M = M`.
- Second consequence: every topological point p with nonsmooth image satisfies
  `β.hom p = p`, so fixation is individual and covers every point above the singular locus.

Dependency declarations read and used:

- Mathlib `Field` (`Algebra.Field.Defs`) and `IsAlgClosed`
  (`FieldTheory.IsAlgClosed.Basic`); no algebraic closure choice is needed in the signature.
- `AlgebraicGeometry.IsIntegral` in `Mathlib.AlgebraicGeometry.Properties`.
- `AlgebraicGeometry.IsHProjective` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
- `AlgebraicGeometry.HasNodalGeometricFibres` in
  `Sheaf.AlgebraicGeometry.NodalGeometricFibres`, including its full geometric tests,
  completed nodal ring and smooth-locus convention.
- `AlgebraicGeometry.Scheme.normalization` and `Scheme.fromNormalization` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`.
- `Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` and the compatible existing
  `Scheme.Pic` in `WeilConjectures.AlgebraicGeometry.PicardFunctor`.
- `Scheme.Pic.instCommGroup`, `Scheme.Pic.mapHom`, and `Scheme.Pic.map` via
  `WeilConjectures.AlgebraicGeometry.Picard.Group`; the latter uses the same recorded
  invertibility notion via its proved interface, not a private copy.
- `Scheme.Modules.degree` in `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`.
- `Scheme.Modules.pullbackComp`, `pullbackCongr` from Mathlib modules, and
  `pullbackObjUnitIso` from the upstream module-sheaf complements.
- `Scheme.Modules.smulHom` in upstream `Cohomology.Defs`.

Proof dependency imports retained: `hProjective_properness` from
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`;
`finite_pinching_invertible_patching` from
`Sheaf.AlgebraicGeometry.FinitePinchingInvertiblePatching`; and
`Scheme.GlobalSectionsBijective.of_isAlgClosed` from the upstream global-sections module.
Mathlib faithful-flat completion, tensor exactness and zero-reflection declarations are
imported from `AdicCompletion.LocalRing`, `AdicCompletion.AsTensorProduct`,
`Flat.FaithfullyFlat.Algebra` and `Flat.FaithfullyFlat.Basic` (the last publicly imports
`Flat.Basic`). The completed-normalization-model proof dependency has no Lean record
and is not imported; it is not needed to type this statement. All nine proof steps and
all their dependency ids are in the theorem docstring for stage 3.

Edge cases checked: integral excludes the empty scheme. No nodes gives an empty ordered
branch type and a unique empty j; injectivity and all fixation assertions are then vacuous,
and the smooth normalization and Picard assertions remain. Genus zero and genus one are
included; no stability or genus bound was added. A rational one-node curve has two opposite
orderings, gluing by z and z inverse, with branch swap acting by inversion. The proof's root
of T^3-T-1 separates them even in characteristic two, so no characteristic exclusion is
present. Several nodes use simultaneous trivialization, preventing an independent change
of scalar on each branch. Field, scheme, and rational point universes are all the existing
scheme universe u; Picard classes retain their actual universe u+1.

Searches actually run with `msearch.py Q77 <item>`:

- LeanFinder: `Picard trivial automorphisms integral projective nodal curve fix ordered
  branches of normalization`: 8 hits, relative normalization/Weierstrass results, none
  supplies this Picard action theorem.
- Loogle: `Picard, normalization`: no hits; unknown identifier Picard was reported.
- Mathlib grep: `Picard|picard|nodal` under AlgebraicGeometry: three incidental Weierstrass
  comments; no curve Picard gluing declaration.
- LeanSearch: `Picard group of integral nodal curve normalization gluing ordered branches`:
  8 hits on relative normalization and ring Picard groups, no exact theorem.
- `rg` in upstream and Sheaf for Picard group, normalized degree-zero, ordered branches,
  gluing scalars and the exact item id. Found the canonical Picard modules used above;
  no duplicate statement or ordered-branch scalar-gluing interface. Read the PicardFunctor,
  Picard/Group, Picard/Degree and degree-point modules; the relative fibrewise degree does
  not replace the node's normalized-degree definition.
- Checked `dag/lean_names_upstream.json` for the new names and the Picard interface.
- DAG definition search found the existing `def-sc-picard-group`, now cited. No existing
  ordered-branch gluing definition node was found. `tools/blueprint_refs.py search
  'ordered branch'` returned 0 matches; `ancestor <item>` returned no ancestor (the
  inherited blueprint.from.node is null).

No statement dispute, statement correction, hollow data, extra theorem, or dependency
interface repair. The helpers only spell out the objects explicitly defined in this
node's statement, using the brief's authorization for same-notion helpers in its own module.
Server compilation through scompile.py is clean, with no errors or warnings; both the
sandbox probe and the actual library module compiled in approximately two seconds each.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
