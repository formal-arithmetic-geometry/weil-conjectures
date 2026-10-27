## Worker report

States AlgebraicGeometry.StablePointedModuli.arithmetic_stable_isom_finite in
Sheaf.AlgebraicGeometry.ArithmeticStableIsomFinite. Its only postponed proof is
that theorem, whose docstring gives all eight DAG proof steps and citations.
No definitions or dependency modules are introduced; no statement is corrected.

Clause-by-clause correspondence:

- Any scheme T: (T : Scheme.{u}); no field, finite-type, Noetherian, normal, or
  reduced hypothesis occurs.
- Genus at least two: (g : ℕ) (hg : 2 ≤ g). This inequality is also recorded
  in each stable-family object; the explicit binder retains the node's hypothesis.
- Two stable unpointed genus-g families: C D : Fiber T g 0 (Over.mk (𝟙 T)).
  The auxiliary ground scheme is T itself and the fibre base is the identity
  T-scheme. Every family over T defines such an object with reflexive base equality,
  so this adds no geometric restriction. The zero is the empty label set.
- Actual curves over T: fiberCurve C and fiberCurve D, reusing the landed
  def-sfb-stable-fiber-curve, which is added to stmt_deps.
- Representing T-scheme: ∃ I : Over T.
- Finite: IsFinite I.hom, the recorded affine-local finite-module notion.
- Unramified: IsUnramified I.hom, locally finite type with open diagonal.
- Universal isomorphism: the existential e is an isomorphism in Over I.left
  of the two actual scheme fibre products, formed by Over.pullback I.hom.
- All tests and isomorphisms: ∀ (V : Over T) (eV : ... ≅ ...).
  No hypothesis restricts V; disconnected and nonreduced tests are included.
- Representing bijections and naturality: ∃! b : V ⟶ I with the displayed
  equality says precisely eV is the pullback of e along b. The pullback.map
  is induced by identity on the original curve, b on parameters, and identity
  on T; its commuting square is Over.w b. Equality after projection to the
  original D is equality of the maps to D_V: their projections to V already
  agree because the maps are over V. The fibre-product property therefore
  gives the full universal-element property and bijections
  Hom_T(V,I) ≃ Isom_V(C_V,D_V), with forward map pulling back e.
- Arbitrary base change: for B→T, a B-map V→I×_T B is canonically a T-map
  V→I. The same universal property gives exactly the same isomorphism.
  Uniqueness makes these identifications commute with every test morphism
  and further base change. Thus the universal-element formulation includes
  the stated arbitrary-base-change compatibility, without extra choices.
- Universal point: V=I and b=id identifies its image with e; its pullback
  along each b is precisely the displayed equation.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom;
  read the structure declarations and docstrings.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  StablePointedModuli, StablePointedModuli.Fiber, and forget.
  Read full family, Hom, Fiber, pullback-properties and pullback definitions.
- Sheaf.AlgebraicGeometry.StableFiberCurve: StablePointedModuli.fiberCurve;
  read its concrete base-equality transport and docstring.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: AlgebraicGeometry.IsFinite;
  read its full affine-local signature and docstring.
- Sheaf.AlgebraicGeometry.UnramifiedMorphism: AlgebraicGeometry.IsUnramified;
  read its entire definition.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:
  pullback, pullback.fst, pullback.snd, pullback.map; read their full signatures.
- Mathlib.CategoryTheory.Comma.Over.Pullback: Over.pullback;
  read its object and map construction, giving actual fibre products.

Plain proof imports cover the recorded, stated proof dependencies, including
CurveLimitPreservation, NoetherianDvrProperness, SchemeUnramifiedEtaleLocality,
ProjectiveBundleProper, UnramifiedBaseChangeOpen, UnramifiedQuasiFinite,
AffineTransitionLimit and the Mathlib finite locality/permanence, Noetherian,
gluing, Yoneda, etale and proper-quasi-finite facts.
lem-sfb-arithmetic-stable-open-bounded, lem-sfb-labelled-stable-isom-unramified,
and lem-sfb-stable-labelled-isom-trait-extension have no recorded Lean statement
in this read clone, so have no proof import yet. They are not typing prerequisites.

Sources read: local Stacks moduli-curves.tex, labels
lemma-curves-diagonal-separated-fp (0DSQ),
lemma-stable-curves-deligne-mumford (0E7A), lemma-stable-separated (0E9A).
Also read the current literature/blueprint/latest proof
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3).
This node is an auxiliary arithmetic diagonal input, not a blueprint unit.

Edge cases checked before writing: g=2 is admitted; g<2 excluded exactly as
in the node. The empty base admits the empty representative and unique empty
universal isomorphism. Nowhere-isomorphic families may have empty Isom scheme.
For C=D, all automorphisms remain in the Iso type, with no quotient or
subsingleton restriction. Nonreduced and disconnected tests are unrestricted.
All schemes use the same arbitrary universe u; no smaller test universe is
introduced. autoImplicit is false and every variable/universe is explicitly bound.

Searches made:

- msearch LeanFinder: "Isom functor of stable curves represented by finite
  unramified scheme over arbitrary base": eight generic scheme-property hits,
  including IsFinite of an isomorphism and FormallyUnramified; no matching theorem.
- msearch Loogle: "AlgebraicGeometry.IsFinite, AlgebraicGeometry.FormallyUnramified":
  zero hits.
- msearch grep: "stable.*[Ii]som|[Ii]som.*stable", AlgebraicGeometry: zero hits.
- msearch LeanSearch: "isomorphisms between two stable genus at least two curves
  are represented by a finite unramified scheme": eight generic morphism-property
  hits, no stable-family representation theorem.
- rg of lean/WeilConjectures and lean/Sheaf for stable/Isom combinations and
  the item id: proof-docstring uses, no arbitrary-base theorem.
  The recorded lem-sfb-stable-isom-finite-unramified concerns field bases only
  and also asserts finite type of the stack; it is not this statement.
- Exact-name searches and dag/lean_names_upstream.json: found the canonical
  StableFiberCurve construction, which is reused, and no duplicate theorem.
  scompile.py --source reports StableIsomFiniteUnramified and
  UnorderedPointedIsom unavailable; no reliance is placed on either module.

Validation: scompile.py compiled the sandbox probe in 3.8 s and library module
in 4.4 s, without errors or warnings. All writes are in the assigned sandbox.
There is no statement dispute, node fault, new node, or dependency repair.

## Second reading by Q37

The dispatcher forbids starting other agents. This is a second pass by the same
worker, not an independent-agent review; the maintainer supplies independent review.
Reopened the node and delivered module: T and every V are arbitrary schemes;
labels are empty; fibre transport reuses the canonical definition; genus and
stability come from the recorded family; finite and unramified are exactly the
dependency notions. Checked that the universal parameter equation projects to
the original D and uses the correct map C_V→C_I. The fibre-product property
makes that projected equality equivalent to pullback of e. Unique parameters
give naturality, arbitrary-base-change compatibility, and the identity universal
point. No mismatch or statement correction was found. The sole added statement
dependency is the existing def-sfb-stable-fiber-curve.

