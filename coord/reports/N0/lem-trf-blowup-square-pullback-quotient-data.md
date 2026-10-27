## Worker report

The module Sheaf.AlgebraicGeometry.BlowupSquarePullbackQuotientData states this node
in two sorry-only theorems: blowupSquare_pullback_quotientData contains the geometric,
local-equation, quasi-coherence, sectionwise kernel, and canonical comparison clauses;
blowupSquare_strictTransform_quotientPresentation states the defining quotient
universal property, applicable to each of the two triples in the first theorem.
No definitions, new nodes, dependency repairs, or statement corrections are needed.

Hypothesis and clause correspondence:

- X,S,Y,T are unrestricted Scheme.{u}; f,e,g,j introduce the four morphisms.
  h : j ≫ f = g ≫ e is precisely fj=eg. [Flat e] and [Flat j] are the two
  assumed flatness conditions; no flatness of f or g is assumed.
- I : S.IdealSheafData encodes the quasi-coherent ideal; [I.toModules.IsFiniteType]
  encodes finite type. B,b are I.blowup,I.blowupMap; B_T,b_T use I.comap e.
  P,Q and their projections are Limits.pullback and pullback.fst/snd.
- The recorded upstream comparison blowupFlatBaseChange e maps to B ×_S T,
  the reverse factor order to the displayed T ×_S B. Its composite with the
  canonical pullback symmetry is exactly the node's comparison. Thus its fst
  is β, and its snd is the map to T. IsIso and the snd equation assert the
  comparison is an isomorphism over T, including the over-T normalization.
- The existential u has hu : u ≫ p = r ≫ j and the explicit second projection
  u ≫ q = s ≫ bc ≫ pr_B. These uniquely specify the pair (jr,βs), rather
  than leaving u arbitrary. IsPullback r u j p supplies the canonical isomorphism
  Q ≅ pullback j p. IsPullback.isoPullback and its hom_fst/hom_snd equations
  are the projection-compatible isomorphism and equations r,u. Flat u is explicit.
- moduleStrictTransformOpen f I is P minus D, directly by its definition.
  The equality moduleStrictTransformOpen g (I.comap e) = u ⁻¹ᵁ
  moduleStrictTransformOpen f I is therefore exactly D_Q = u⁻¹D as closed sets.
  This asserts no equality of closed subscheme structures.
- The pointwise existential supplies an affine open V containing every x and
  a section a. V ⊓ moduleStrictTransformOpen f I = P.basicOpen a is precisely
  D∩V=V(a), with both sides complemented inside V. The universally quantified
  affine W and hW : W ≤ u⁻¹ᵁV give the corresponding equation for D_Q∩W,
  using the actual image (u.appLE V W hW) a, for every such W. Neither section
  is assumed to be a nonzerodivisor.
- For every F : X.Modules with [F.IsQuasicoherent], the ordinary pullbacks H
  and H_Q are explicitly the tensorPullback objects along p, respectively j and r.
  Their IsQuasicoherent clauses are explicit. The auxiliary j*F quasi-coherence
  and I.comap e finite-type facts supply the conditions required to instantiate
  the second strict-transform definition; the node's proof explicitly derives
  these in steps 3 and 4. They are conclusions, never extra assumptions.
- K and K_Q are the recorded moduleStrictTransformKernel objects, hence actual
  kernels of the recorded restriction maps. Both have IsQuasicoherent clauses.
  On every open V (respectively W), Set.range of the kernel inclusion on sections
  is precisely the set whose restriction to V∩Dᶜ (respectively W∩D_Qᶜ) is zero.
  The restriction arrow is homOfLE inf_le_left, mapped by the actual module
  presheaf. These equalities specify the supported submodules, including their
  inclusions, rather than asserting merely some abstract kernel isomorphism.
- The second theorem uses moduleStrictTransform f I F itself as the quotient
  object, and cokernel.π (kernel.ι (moduleStrictTransformRestriction f I F))
  as its defining quotient map. The unique factorization is the quotient
  universal property H/K. Instantiating with (g,I.comap e,j*F), using the
  auxiliary facts above, gives exactly H_Q/K_Q and π_Q. The recorded definition
  is literally this cokernel, so no extra identification is chosen.
- The existential γ has source u*H and target H_Q. Its equality fixes it as
  (tensorPullbackSectionComp u p).symm.app F, followed by eqToIso of hu,
  followed by (tensorPullbackSectionComp r j).app F. These are exactly the
  normalized composition isomorphisms and pu=jr named in the node.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom;
  Scheme.Hom.appLE is the section ring map; Scheme.basicOpen gives nonvanishing.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat, with the
  stalkwise equivalence Flat.iff_flat_stalkMap, matching the recorded dependency.
- Sheaf.AlgebraicGeometry.CoherentFiniteType: the recorded module exposes
  SheafOfModules.IsQuasicoherent and IsFiniteType, the node's separate notions.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: tensorPullback,
  tensorPullbackSectionComp and tensorPullbackSectionAdjunction. The latter
  is uniquely normalized on 1 tensor m, fixing the chosen composition comparison.
- WeilConjectures.Blowup.Gluing: Scheme.IdealSheafData.blowup and blowupMap.
- Mathlib.AlgebraicGeometry.IdealSheaf.Functorial: IdealSheafData.comap.
- WeilConjectures.Blowup.FlatBaseChange: IdealSheafData.blowupFlatBaseChange,
  blowupFlatBaseChangeIso and blowupFlatBaseChangeIso_hom_snd; the recorded
  audit declaration for def-nagata-blowup-flat-base-change-map is used directly.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback,
  pullback.fst and pullback.snd; IsPullback and its canonical isoPullback
  supply the projection-compatible cartesian isomorphism.
- Sheaf.AlgebraicGeometry.ModuleStrictTransform: moduleStrictTransformOpen,
  moduleStrictTransformRestriction, moduleStrictTransformKernel,
  moduleStrictTransform. Their definitions and docstrings were read in full.

The plain imports include the stated proof dependencies
WeilConjectures.Blowup.Principalization (isInvertible_comap_blowupMap) and
WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
(isQuasicoherent_pullback). The flat-base-change proof dependency is in the
publicly imported flat-base-change module. The flat morphism base change node
and locally-principal supported-kernel node have no recorded modules, so there
are no nonexistent imports for them. The former property is exposed by Mathlib's
imported Flat.isStableUnderBaseChange. The latter is a stage-3 proof dependency,
not a missing notion needed to type this statement.

Sources read: literature/stacks-project/divisors.tex, lemma-flat-base-change-blowing-up
(Tag 0805), lemma-blowing-up-gives-effective-Cartier-divisor (Tag 02OS), and the
paragraph preceding definition-strict-transform and clause (1) (Tag 080D).
The six proof steps of the DAG are retained in the main theorem's docstring.

Edge cases checked: empty schemes and empty affine opens are allowed; no Nonempty
or nontrivial-ring hypothesis occurs. I=0 produces the empty blowup and vacuous
pointwise charts, as required. I=O has empty exceptional set and supported kernels
zero. F=0 is included. The square need not be cartesian to start with: only its
commutativity is assumed. No finiteness of F, separatedness, Noetherian property,
or flatness of f or g is introduced. Nilpotent equations and zero divisors are
allowed in the local chart clause. One common arbitrary universe u is the
existing scheme/module framework's universe; there is no independent test-object
universe or coefficient-size restriction.

Searches actually run using msearch.py (N0, this item):

- LeanFinder: "Flat blowup square cartesian comparison locally principal exceptional
  closed sets quasi coherent strict transform quotients": eight results,
  Flat.flat_appLE, Flat, Flat.generalizingMap, Scheme.Hom.flat_appLE,
  flat_iff, Flat.instResLE, Flat.instIsMultiplicativeScheme and
  Flat.instOfIsOpenImmersion. None states these quotient and kernel data.
- Loogle: '"tensorPullbackSectionComp", "blowupFlatBaseChange"': zero results.
- grep: 'strictTransform|strict_transform|blowup' in AlgebraicGeometry: zero hits.
- LeanSearch: "Blowup flat base change cartesian square and supported section
  quotient presentations of strict transforms": eight base-change/flatness hits,
  including Flat.isStableUnderBaseChange; none supplies this combined statement.
- rg over lean/WeilConjectures and lean/Sheaf located the existing strict-transform
  modules, kernel theorem and flat-pullback theorem. The latter states an
  isomorphism of strict transforms but does not assert this node's affine chart,
  supported-kernel sectionwise descriptions, and ordinary-pullback quotient data.
  It was not imported: its canonical helpers would make the upstream proof plan
  depend on the parent theorem's module. The current statement uses the existing
  primitive objects directly and uniquely characterizes its map and comparison.
- rg for the node id and proposed theorem names in WeilConjectures, Sheaf, Mathlib
  and dag/lean_names_upstream.json found no existing statement with this content
  and no collisions of the two new names.

Validation: scompile.py checked the actual sandbox module. Initial elaboration
repairs qualified Limits.pullback, its scheme category, and ring sections to
avoid the unrelated Scheme.Modules.pullback and overloaded section notation.
Three lines were subsequently wrapped to the 100-character convention.
No mathematical statement change and no disputed clause.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
