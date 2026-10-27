## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeUCSurjectionSeparated`
states `AlgebraicGeometry.AlgebraicSpace.mapIsSeparated_of_surjective_universallyClosed`,
with the entire proof postponed by `sorry`. It is exactly Stacks Project, Morphisms of
Spaces, Tag 05Z2(4), read at `lemma-image-universally-closed-separated` in
`literature/stacks-project/spaces-morphisms.tex`. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read. No definitions are introduced or copied.

Hypothesis and conclusion correspondence:

- The scheme S is `{S : Scheme.{u}}`; `universe u` is explicit and `autoImplicit` is false.
  The scheme universe and the existing algebraic-space category provide the fixed
  size convention without a further object or a restriction on S.
- The three algebraic spaces over S are `(B U V : AlgebraicSpace S)`. In particular
  B is an algebraic space, with no assumption of representability or separatedness over S.
- The three maps are `(p : U ⟶ B) (q : V ⟶ B) (a : U ⟶ V)`.
  These are morphisms in the existing full subcategory of fppf sheaves, hence natural
  transformations. The equation q composed with a equals p is `(hcomm : a ≫ q = p)`.
- Surjectivity of |a| is `(hsurj : Function.Surjective (mapPoint a.hom.hom))`.
  This does not require representability of a, nor scheme-test representability.
- Universal closedness is `(hclosed : MapIsUniversallyClosed a)`. Its recorded
  definition quantifies over every `(Y' : AlgebraicSpace S)` and `(g : Y' ⟶ V)`
  and requires `IsClosedMap (mapPoint (Limits.pullback.snd a.hom g.hom).hom)`.
  This is precisely the stated sheaf-fibre-product projection with atlas topology.
- Separatedness of p is `(hsep : MapIsSeparated p)`. Its recorded definition is
  `IsRepresentableWith (fun _ _ r ↦ IsClosedImmersion r.left)
  (pullback.diagonal p.hom.hom)`. The representability predicate asks for a scheme
  representing each scheme test of the relative diagonal, with its projection a
  closed immersion. It uses the relative square over B, not over S or Spec Z.
- The conclusion `MapIsSeparated q` uses exactly the same scheme-test condition
  on the relative diagonal of q.
- There are no finite-type, quasi-compactness, Noetherian, flatness, or separation
  assumptions on B/S or on any other map besides those in the statement.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
  The full signatures and docstrings were read in the pinned Mathlib source.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, and `AlgebraicSpace.IsRepresentableWith`.
  The last predicate supplies actual representing pullback squares over each test scheme.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, including the universal-property clause.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace` and its final-topology construction.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding with surjective stalk maps).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsSeparated` and `AlgebraicSpace.MapIsUniversallyClosed`.
  This already landed definition node is added to stmt_deps under the explicit rule
  allowing landed statement dependencies. Every other field besides lean is preserved.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint`, available
  through the morphism-properties module; it maps field-valued point classes by the
  underlying natural transformation and is a genuine quotient map construction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`:
  `AlgebraicSpace.point_open_calculus`, imported without public as a stated proof dependency.
  Its full signature and docstring were read, especially compatible-point lifting and
  continuity for arbitrary morphisms.
- `lem-sfb-space-separated-diagonal-closed` is a proof dependency without a Lean record
  in the current DAG. It is named in the complete natural-language proof docstring;
  there is no module to import for it. It is not needed to elaborate this statement.

The docstring reproduces all four proof steps: factor the product map into base
changes of a; compose with the separated diagonal of p; cancel the surjective
point map after an arbitrary test using the closed-set image equality; and use
recognition of a universally closed relative diagonal as a closed immersion.

Edge cases checked before writing: when U is empty, point-surjectivity forces V
empty, so the conclusion is consistent. For a the identity, commutativity identifies
p and q and the assertion specializes to the given separatedness. The base B may
be nonseparated over S or empty; neither case is excluded. The universal-closedness
test includes identities and arbitrary algebraic-space base changes. No field
characteristic, index nonemptiness, or dimension is constrained.

Searches made before writing:

- `msearch.py ... leanfinder "Separatedness of algebraic spaces over an arbitrary
  algebraic space descends along a surjective universally closed morphism"`: eight
  scheme-property hits, including `instHasOfPostcompPropertySchemeUniversallyClosedIsSeparated`;
  none is this relative algebraic-space result.
- `msearch.py ... loogle "AlgebraicGeometry.IsSeparated, AlgebraicGeometry.UniversallyClosed"`:
  five scheme-only hits, including `UniversallyClosed.of_comp_of_isSeparated` and
  `isProper_iff`; no match.
- `msearch.py ... leansearch "Separatedness descends along a surjective universally
  closed morphism of algebraic spaces over an arbitrary algebraic-space base"`:
  eight scheme-only hits, including `UniversallyClosed.of_comp_surjective`; no match.
- `msearch.py ... grep "AlgebraicSpace|universallyClosed.*[Ss]eparated|[Ss]eparated.*universallyClosed"
  AlgebraicGeometry`: six hits in scheme modules Proper and ZariskisMainTheorem; no match.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for `AlgebraicSpace`, universal-closedness
  and separation patterns, and the proposed declaration name; `grep -rn` for the item id
  on `lean/WeilConjectures`: no existing declaration for the item. The upstream module
  `IsSeparatedOfSurjectiveUniversallyClosed` concerns schemes only. The existing
  `AlgebraicSpaceUCSurjectionSeparation` module was read in full: its theorem is the
  absolute affine-pair test for 05Z2(1),(2), not relative separatedness over arbitrary B.
- The existing morphism-properties definitions were found and read in full, rather
  than restated. The proposed full declaration name has no existing source/index hit.

Validation: scompile.py compiled the file both as sandbox and as its library module,
with no errors or warnings (5.4 seconds and 1.5 seconds respectively). All compiles
use the prescribed server wrapper. No new nodes, dependency modules, statement
corrections, or disputed statements are needed.

## Second reading by Q41

A separate pass by this worker reopened the node and completed Lean file; no other
agent was started, as instructed by the dispatcher. Checked every binder against the
node and Tag 05Z2(4): B remains an arbitrary algebraic space, the commutativity equation
has the correct orientation, surjectivity is on point classes and does not assume
representability of a, and both separatedness predicates use their relative diagonals.
Unfolded the recorded universal-closedness and separatedness definitions in their source
modules and verified their scheme tests and atlas topology. The only dependency-list
addition is the already landed def-sfb-space-morphism-properties, needed to cite those
shared predicates. The main theorem has no extra clause and no missing hypothesis.
No mismatch was found and no statement correction was made. This is a self rereading;
the maintainer's independent review is still separate.
