## Worker report

Module: `Sheaf.AlgebraicGeometry.AdequateProductAffinization`.
Main declaration: `CategoryTheory.adequate_product_affinization`.
The only theorem has proof `sorry`. The two auxiliary declarations have actual
terms: `moduliSelfProduct` is the existing 2-fibre product of the existing base
structure maps, and `moduliRepresentableSchemeMap` is the Yoneda preimage with
source transported along the based functor's projection equality. No definition
chooses unspecified data or contains a postponed proof.

The node is unchanged except for its `lean` record. No new nodes, dependency
repairs or mathematical statement corrections are needed.

Clause-by-clause rendering:

- The field is `(k : Type u) [Field k]`.
- The stack over k is `F : BasedCategory.{v, w} (Over (Spec (.of k)))` with
  `hF : IsAlgebraicModuliStack F`. This is the recorded algebraic-stack notion,
  allowing an algebraic-space diagonal and smooth surjective scheme atlas.
- Finite type is `hft`: existence of a scheme `U` over k and a smooth surjective
  scheme atlas `a`, expressed by `IsSmoothModuliAtlas F U a`, for which
  `LocallyOfFiniteType U.hom` and `QuasiCompact U.hom` hold. This tests finite
  type on a smooth scheme atlas. It does not assert that U is smooth over k,
  nor impose the DM-specific finite-type-etale-atlas notion.
- The affine k-scheme is `(Y : Over (Spec (.of k))) [IsAffine Y.left]`.
- The given k-morphism is the based functor `φ` into the representable groupoid
  `discreteModuli (yoneda.obj Y)`.
- Its adequacy hypothesis is the actual recorded predicate
  `IsAdequateModuliSpace F hF (AlgebraicSpace.schemeSpace Y) φ`.
  `schemeSpace` is the existing representable algebraic space of Y, with the
  same Yoneda presheaf. Its use introduces no extra atlas hypothesis.
- The stack product is `moduliSelfProduct F`, defined as
  `moduliTwoFiberProduct (moduliBaseStructure F) (moduliBaseStructure F)`.
  The base stack is the identity category over Sch/k, representing Spec k.
  The product retains the comparison isomorphism and all arrows; it is not a
  product of isomorphism classes or an ordinary scheme pullback. The output
  `hW` witnesses algebraicity, needed to apply the existing adequate predicate.
- The actual ring of global functions is
  `moduliGlobalSectionsRing (moduliStructureSheaf (moduliSelfProduct F) hW.1.1)`.
  These are compatible section families, with the already recorded canonical
  ULift transport. It lies in a larger universe than `Scheme.{u}`. The output
  `B : CommRingCat.{u}` and ring equivalence `e` present exactly this ring in
  the scheme universe. They are existential conclusions, not a smallness
  hypothesis and not replacement of global functions by an arbitrary ring.
  A qc scheme atlas makes the global-function ring small: restriction embeds
  it into the ring of functions on that atlas. Thus this representation
  excludes no stack allowed by the node. The displayed ring equivalence is
  available to consumers; no anonymous arbitrary choice is used downstream.
- `Spec B` is the stipulated affine spectrum, in this small presentation.
  The output `q : Spec B ⟶ Spec (.of k)` supplies its k-structure, and the
  output based functor `ψ` is a k-morphism to its representable groupoid.
- The canonical-map characterization is the first conjunct in the output:
  for every total scheme object `x` and every `b : B`, pullback of b along
  `moduliRepresentableSchemeMap ψ x` equals evaluation of the global section
  `e b` at x. `(Scheme.ΓSpecIso B).inv` identifies b with the corresponding
  global function on Spec B; `.down` removes precisely the existing ULift.
  This is a characterization on all scheme objects, hence in particular on
  every smooth affine chart. Maps to an affine scheme are determined by
  pullback of functions, so this pins down the canonical map, rather than
  asserting adequacy of an unconstrained morphism. Presenting the canonical
  ring and map by their existence and defining characterization is equivalent
  to the node's notation `B = Γ(X×X,O)` and its canonical ψ.
- The final conjunct is
  `IsAdequateModuliSpace (moduliSelfProduct F) hW
    (AlgebraicSpace.schemeSpace (Over.mk q)) ψ`.
  It includes qcqs, the structure-sheaf isomorphism, and lifting on every
  affine etale base change for every quasicoherent algebra on that base change,
  exactly as in the recorded definition.
- There is no quasi-finiteness, finiteness, separatedness, representability-by-
  schemes or DM hypothesis on the diagonal. Universes u, v and w are explicit
  and independent, and `autoImplicit` is false.

Dependencies read and used:

- `Field`, Mathlib.Algebra.Field.Defs: the standard nontrivial field class.
- `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`, Mathlib.AlgebraicGeometry.Scheme:
  the recorded scheme and spectrum declarations.
- `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: finite type
  of the atlas structure morphism is their conjunction.
- `CategoryTheory.IsAdequateModuliSpace`,
  Sheaf.AlgebraicGeometry.AdequateModuliSpace: the precise supplied definition.
- `IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`,
  Sheaf.AlgebraicGeometry.AlgebraicModuliStack, publicly available through the
  adequate definition: the supplied algebraic-stack and smooth-atlas notions.
- `moduliTwoFiberProduct`, `discreteModuli`,
  Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: existing 2-fibre product
  and representable groupoid constructions, available transitively.
- `moduliBaseStructure`, Sheaf.AlgebraicGeometry.RelativeModuliInertia: the
  recorded structural map to the identity fibred category.
- `moduliSchemeForget`, `moduliStructureSheaf`, `moduliGlobalSectionsRing`,
  Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra: actual structure sheaf and
  compatible-family ring, available through the adequate definition.
- `AlgebraicSpace.schemeSpace`, Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite:
  the existing scheme-as-space construction. Read its actual declaration and
  source docstring; no second scheme-as-space definition is introduced.
- `Scheme.ΓSpecIso`, Mathlib.AlgebraicGeometry.Scheme, and the scheme/affine
  adjunction in Mathlib.AlgebraicGeometry.GammaSpecAdjunction: the normalization
  of the chart pullback condition. The latter import exposes the standard
  affine-target adjunction used to interpret that condition.
- The only already stated proof-only dependency not otherwise public is
  Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism, imported privately.
  All six other proof-only nodes currently lack Lean records, so their
  modules cannot yet be imported. Their steps are retained in the theorem
  docstring. None is needed merely to type this statement: algebraicity and
  the canonical affinization are supplied in its conclusion.

Source check: read the primary PDF https://arxiv.org/pdf/1005.2398v3,
Theorem 8.3.2, printed pp.39--40, including the product relative-Spec
construction in the proof of (3) implies (1). The construction, rather than
that theorem's separate diagonal-finiteness application, is the assertion
formalized here. The node's four proof steps are reproduced in the docstring:
affine-target criterion and composition, base change over Spec k, composition
for the product, and canonical qcqs affinization with global power lifting.

Edge cases checked mathematically before drafting: the empty stack and empty
affine target are allowed; in this case B may be the zero ring and Spec B is
empty. No `Nontrivial B`, nonempty atlas, positive dimension, perfectness of k,
or characteristic-zero assumption appears. Non-DM examples such as classifying
stacks of positive-dimensional geometrically reductive groups are not excluded.
Nonreduced objects are allowed. The small presentation is supplied by the
conclusion, so arbitrary endpoint category universes are retained. The defining
pullback equation is well typed also for nonaffine scheme objects.

Searches (2026-10-24):

- msearch.py LeanFinder: `The canonical affinization of the product of an
  algebraic stack with affine adequate moduli space is an adequate moduli space`.
  Eight scheme-affineness/affine-morphism hits; no adequate-moduli theorem.
- msearch.py Loogle: `IsAdequateModuliSpace, affinization`.
  Zero hits, unknown Mathlib identifier IsAdequateModuliSpace.
- msearch.py grep: `adequate|Adequate|affinization|Affinization`,
  AlgebraicGeometry. Zero Mathlib hits.
- msearch.py LeanSearch: `An algebraic stack with an adequate moduli space to
  an affine scheme has adequately affine self product affinization`.
  Eight scheme-affineness hits, including isAffine_of_isAffineHom, the IsAffine
  constructors and affine pullbacks; none states the stack assertion.
- rg in lean/WeilConjectures for adequate/Adequate/affinization/Affinization:
  only the unrelated derived-global-sections scheme affinization comparison.
- grep -rn for this item ID in lean/WeilConjectures: no hits.
- rg in lean/Sheaf for affinization and finite-type/stack/global-section notions:
  located the existing adequate definition, structure ring, qcqs, atlas and
  2-fibre product modules listed above; no product-affinization theorem.
- rg for moduliSelfProduct, moduliRepresentableSchemeMap and
  adequate_product_affinization in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json: no declaration-name collisions.

Compilation: prescribed scompile.py checked the single delivered file in both
sandbox and library mode, exit 0, with no non-sorry warnings (6.3 s and 9.8 s).
The example CompactObject.lean and its node record were read; its current source
is withdrawn, so the normal module/public-import/exposed-section convention of
the live dependency modules is used. No disputed statement or node fault found.

## Second reading by Q38

This is a second in-session reading by the same worker; no other agent was
started, as the dispatcher's brief prohibits it. The maintainer supplies the
independent review. I reopened the node and the completed file and checked the
match again. `IsSmoothModuliAtlas` is used rather than the available DM-specific
`HasSmoothFiniteTypeModuliAtlas`, which would add smoothness of U over k and
etaleness of the atlas. The finite-type hypothesis is exactly finite type on a
smooth atlas. The product uses the structural maps, not φ, so it is over k and
not over Y. The ring is the structure ring of that product, not Γ(X,O) tensor
itself. The output equivalence identifies every element of B with an actual
compatible global family; the equation at every total scheme object identifies
ψ canonically and fixes the direction of ΓSpecIso. The final predicate uses
this same ψ and includes all affine-etale algebra tests. Empty and zero-ring
cases remain. No mismatch requiring a change was found.
