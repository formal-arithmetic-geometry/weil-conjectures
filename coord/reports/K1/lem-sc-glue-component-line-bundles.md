## Worker report

The module states the gluing assertion from Varieties Lemma 09NE. It binds a reduced scheme `Y`, a finite family of schemes and closed immersions covering `Y`, discrete pairwise intersection spaces, and invertible modules on each component. The first conjunct asserts existence of an invertible module on `Y` restricting by pullback to each component. The second conjunct states the prescribed-section version: sections whose germs are nonzero at every pairwise intersection admit an invertible module and compatible pulled-back global sections.

The Lean declaration is `AlgebraicGeometry.glueComponentLineBundles` in `lean/Sheaf/AlgebraicGeometry/GlueComponentLineBundles.lean`. `IsReduced`, `Scheme`, `IsClosedImmersion`, `Scheme.Modules`, `Scheme.Modules.IsInvertible`, `Γ`, and stalk germs are the Mathlib/upstream declarations used. The family index is `Fin r`, allowing `r = 0`; the cover hypothesis then correctly becomes impossible. For `r = 1`, the discreteness premise is vacuous. Empty intersections are represented by the corresponding subtype and impose no germ conditions.

Searches: `msearch.py ... leanfinder "glue invertible sheaves and global sections on reduced components"` (no exact declaration); `msearch.py ... loogle "AlgebraicGeometry.IsInvertible, gluing sheaves"` (generic APIs only); `rg` over Mathlib AlgebraicGeometry and WeilConjectures (no matching theorem). The dependency declarations are Mathlib `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsReduced`, `AlgebraicGeometry.IsClosedImmersion`, and upstream `AlgebraicGeometry.Scheme.Modules.IsInvertible` from `WeilConjectures.AlgebraicGeometry.Modules.Invertible`.

## Earlier second reading (a previous round; superseded)

The node and file were read together. All hypotheses (reducedness, finite closed cover, discrete intersections, invertible component modules) occur as explicit binders. The two conclusions are represented as the two conjuncts. The section clause uses a family of sections of the pullbacks, with each identified with the prescribed component section by an isomorphism; this is the typed Lean rendering of restriction compatibility.

## Second reading by K1

Independent reading on 2026-10-11, with the node, module and Stacks source open.
The repository's literature checkout is absent here; I read the local Stacks
sources `/home/ubuntu/c1-stacks-review/varieties.tex`, lines 7990–8088,
`modules.tex`, Lemma `lemma-s-open` (01CY), and `properties.tex`, Section 01PR.
Varieties 09NE introduces an arbitrary scheme, not a scheme over a field;
the chapter's ground-field notation adds no hypothesis to this lemma.
The node's mathematical statement is correct and remains unchanged.
The previous worker report's section-clause and empty-cover assessments are
superseded by this reading and the repairs below.

Objects, hypotheses and conclusions, item by item:

- Finite closed family `Z_1,…,Z_r`: `{r : ℕ}`, `Z : Fin r → Scheme.{u}`,
  `f : ∀ i, Z i ⟶ Y`, `hf : ∀ i, IsClosedImmersion (f i)`. Exact: no
  irreducibility or reducedness of the individual closed subschemes is assumed.
- Ambient reduced scheme: `Y : Scheme.{u}`, `hY : IsReduced Y`. Exact.
  I read `def-pc-scheme`, `def-pc-reduced-scheme` and their Mathlib declarations:
  Scheme is locally affine as a locally ringed space; reducedness is defined
  sectionwise, with the stalkwise equivalence in Properties.lean.
- Set-theoretic cover: `hcover : ∀ y : Y, ∃ i, ∃ z, (f i).base z = y`.
  Exact. Closed immersions give the component subsets, with no stronger
  scheme-theoretic-cover hypothesis.
- Discrete distinct pairwise intersections: `hdiscrete` applies
  `DiscreteTopology` to the subtype of points lying in both images for `i ≠ j`.
  Exact: this is the induced topology of the underlying intersection.
  I read `def-weil-closed-immersion` and Mathlib ClosedImmersion.lean: its
  closed embedding and surjective stalk maps are precisely the needed notion.
- Component invertible modules: `M : ∀ i, (Z i).Modules`, `hM : ∀ i,
  Scheme.Modules.IsInvertible (M i)`. Exact. I read `def-sc-invertible-module`
  and upstream Invertible.lean: `exists_isoUnit` means locally the structure
  sheaf, hence locally free of rank one and quasi-coherent. The dual clause
  of that definition node is not needed for this theorem.
- First conclusion: `∃ N : Y.Modules, IsInvertible N ∧ ∀ i,
  Nonempty ((pullback (f i)).obj N ≅ M i)`. Exact existence and restriction
  up to isomorphism, with no uniqueness assertion.
- Prescribed component sections: `∀ s : ∀ i, Γ(M i, ⊤)`, followed by the
  intersection nonvanishing premise. Corrected to membership in
  `Scheme.Modules.nonvanishingLocus`. I independently read the landed
  `Sheaf.AlgebraicGeometry.Ample` declaration and its node
  `def-weil-pbc-ample-invertible-module`: it is the germ outside the maximal
  ideal times the module stalk, exactly the nonzero residue-field fibre in
  Stacks 01CY/01PR. Its definition has no invertibility or ampleness argument,
  so importing it adds no quasi-compactness or ampleness hypothesis.
  Both component values are required for two preimages of the same point,
  which is exactly the source's condition for all distinct pairs.
- Second conclusion: corrected to `∃ N : Y.Modules, ∃ t : Γ(N, ⊤), …`.
  The same single `t` must pull back to `s i` under an isomorphism `e` for
  every component. The displayed equality uses the unit of the existing
  `Scheme.Modules.pullbackPushforwardAdjunction` at `N`, evaluated at `⊤`,
  followed by `e.hom.app`. Its target open is `(f i) ⁻¹ᵁ ⊤`, which is the
  whole component. Restricting `s i` along `homOfLE le_top` expresses that
  equality without an implicit transport between equal opens. Exact.
  I read Mathlib Modules/Sheaf.lean (`Modules`, `pullback`, the adjunction,
  and the pushforward section formula), and upstream FreeGenerator.lean's
  `pullbackSection`, which uses this same unit. No private pullback notion.

Mismatches and repairs:

1. H3: nonzero stalk germ is weaker than nonvanishing in the fibre. For the
   trivial line bundle on `Spec k[x]`, section `x` has a nonzero germ at
   `(x)` but zero residue-field value there. Replaced germ inequalities by
   the existing `nonvanishingLocus`; imported its landed module and added
   its owning node to `stmt_deps`. No new definition node is needed.
2. H3: separate sections `t i` on pullback modules do not assert any global
   section on `Y`; indeed they can be obtained from `s i` by each inverse
   isomorphism alone. Replaced them by one `t : Γ(N, ⊤)` and its canonical
   pullbacks. This repairs the Lean, not the node's mathematical statement.
3. H8/H9: added the project license header and all four natural-language
   proof steps, explicitly naming the two supporting DAG nodes. Removed
   the now-redundant direct module imports in favour of the used Ample
   module. No definitions or additional theorems were written; the theorem
   proof remains solely `sorry`.

Edge cases: `r = 0` forces `Y` empty by `hcover`, not an impossible cover
in all cases as the worker report claimed. On the empty scheme the structure
module and its unique zero section meet both conclusions. Empty components
and empty pairwise intersections impose no nonvanishing conditions. For
`r = 1` the pairwise premise is vacuous and any section can be used. Zero
sections on components with actual intersections are correctly excluded;
on disjoint components they are allowed. The zero module on an empty scheme
is locally invertible vacuously. Repeated nonempty components are allowed
when their common underlying space is discrete. No characteristic, field,
Noetherian, separatedness, dimension or nonemptiness hypothesis is added.
`universe u` is explicit and arbitrary; the finite indexing by `Fin r`
covers every finite family after enumeration. Mathlib's scheme morphisms
use a common universe; every finite collection of schemes can be placed
in a common sufficiently large universe. No autoimplicit variable remains.

Independent searches, with wording different from the first worker:

- `msearch.py … leanfinder "line bundles on finite closed covering with
  discrete overlaps and prescribed global section"`: eight generic
  open-cover/sheaf-gluing results (including `TopCat.Sheaf.existsUnique_gluing`
  and `Scheme.OpenCover.ext_elem`), no exact closed-cover statement.
- `msearch.py … leansearch "invertible sheaves gluing over closed subschemes
  with discrete intersections"`: service HTTP 500; unavailable, no verdict.
- `msearch.py … loogle '"glue", "invertible"'`: zero hits.
- `rg -n -i 'glue.*(invertible|line.?bundle)|discrete.*intersection|
  nonvanishing|nonVanishing'` across Mathlib AlgebraicGeometry, the complete
  upstream WeilConjectures tree and repository `lean/Sheaf`: upstream
  Descent.lean gives fpqc descent, not this finite closed-cover theorem;
  the project Ample.lean supplies the exact nonvanishing predicate reused
  here. No theorem with this statement was found. Searching
  `glueComponentLineBundles` in all three trees and `dag/lean_names_upstream.json`
  found no existing declaration. Searches of DAG records located the
  already-landed nonvanishing declaration on its owning ample-definition
  node; no duplicate notion or additional dependency module is introduced.

Validation: compiled the repaired single module with `scompile.py K1
lem-sc-glue-component-line-bundles` on the server: exit code 0, 1.9 seconds,
no warnings. The node's `lean.statement` is the exact multiline signature
from `theorem` through its result type before `:=`, and the unchanged node
statement and proof agree with the source. All lines are within 100 characters.
