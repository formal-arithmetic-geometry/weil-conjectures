## Worker report

The module `Sheaf.AlgebraicGeometry.OrbitTensorLineDescent` states
`AlgebraicGeometry.Scheme.Modules.orbit_tensor_line_descent`. Its proof is `sorry`.
Seven real-data helper definitions implement local section transport, orbit frames,
pure tensor sections, and the normalized pullback comparisons. They are part of the
canonical maps in this node, not separately postulated mathematical input. No data
is chosen from an unproved existence statement. All variables and universes are
explicit, and both auto-implicit options are disabled.

The orbit tensor itself is the already landed `pencilOrbitBundle`, not a new
construction. The recorded module is absent from this machine's read clone; I read
its complete current source using
`scompile.py --source Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil`.
The owning node `def-sfb-pencil-orbit-bundle-norm` is added to `stmt_deps` under the
standing authorization to cite an already landed definition node. Nothing else in
the node is changed except `lean`. No new node or dependency repair is needed.

Hypothesis and clause correspondence:

- Schemes X and Y are `{X Y : Scheme.{u}}`. The finite group has independent size
  `H : Type v`, `[Group H]`, `[Finite H]`. Automorphisms are `a : H → (X ≅ X)`.
  `a_one` is the identity law; `a_mul` says a_(gh) = a_g composed with a_h, with
  Lean's composition written `(a h).hom ≫ (a g).hom`. This is exactly the node's
  a_h composed with a_g = a_(hg), after renaming the variables.
- The quotient is `q : X ⟶ Y` with `[IsFinite q]` and `[Surjective q]`.
  `aq` is `(a h).hom ≫ q = q` for every h. In particular every `q ⁻¹ᵁ T` is
  invariant. Each equality of inverse-image opens in the statement is the
  congruence of this specified scheme-morphism equality, not an extra hypothesis.
- `ring_injective` says the actual canonical structure map `q.app T` is injective
  on every open. `ring_image` says its image is exactly the fixed functions under
  each actual pullback `(a g).hom.app`. Transport between equal opens uses the
  structure presheaf's restriction. Together these give the canonical ring
  isomorphism O_Y(T) = O_X(q⁻¹T)^H. It commutes with restrictions because `q.app`
  is the scheme's structure-sheaf map; this is not a separately selected ring map.
- L is `L : X.Modules` with `[L.IsInvertible]`. N is exactly
  `pencilOrbitBundle a L`, the right-associated finite tensor of the actual
  `tensorPullback (a h).hom` applied to L, terminating in the tensor unit.
  The enumeration is the owning definition's `pencilGroupElements H`.
- `lin g` is an O_X-linear isomorphism a_g^*N ≅ N. The first two conclusion
  clauses give its identity and cocycle laws, using normalized identity and
  composition comparisons. The frame equation says it fixes the tensor of
  the translates of every section s on q⁻¹T. In particular it fixes every orbit
  frame. By the imported finite-trivialization theorem, such frames generate
  over a cover pulled back from Y, so this equation uniquely determines the
  canonical factor-permutation linearization, including its action on arbitrary
  scalar multiples. It does not allow an arbitrary linearization fixing only
  some chosen section. `linPow` has the same laws and fixes the pure power of
  each orbit frame, so it uniquely determines the induced tensor-power action.
- The invariant sheaf is specified by `M : Y.Modules` and the inclusion
  `j : M ⟶ (pushforward q).obj N`. `j.app T` is injective for every T and its
  image is exactly the sections fixed by `lin g` for every g. This is the
  usual characterization of the sheaf T ↦ N(q⁻¹T)^H, with its actual inclusion
  and inherited O_Y-module structure. It determines the pair (M,j) up to a
  unique inclusion-preserving isomorphism; it does not merely assume that a
  descended object exists. Naturality and Y-linearity are included in j's type.
- `M.IsInvertible` is the first clause after these witnesses. The isomorphism
  `e : (tensorPullback q).obj M ≅ N` is required to have its forward map exactly
  equal to the adjoint of j under `tensorPullbackSectionAdjunction q`. Thus it
  is the canonical evaluation map. Its equivariance is the displayed equality
  `(tensorPullback (a g).hom).map e.hom ≫ (lin g).hom =
  (orbitQuotientPullbackIso q (a g).hom (aq g) M).hom ≫ e.hom`.
  The comparison on q^*M is explicitly constructed from q a_g = q and the
  section-normalized pullback-composition isomorphism.
- For every `d : ℕ`, `c d` is the natural map from M's existing tensor power
  into q_* of N's existing tensor power. The equation on `orbitPowerSection`
  specifies its action on every pure tensor of arbitrary sections of M.
  Its components are injective and have image exactly the sections fixed by
  `linPow d`. Consequently its factorization through the invariant subsheaf
  is an isomorphism: on each open this factorization is bijective, and the
  inverses commute with restriction by uniqueness. This expresses precisely
  the node's isomorphism M^d → (q_*(N^d))^H, without introducing an arbitrary
  object representing the target. `tensorPow 0` is the structure sheaf, and
  the separate formula on every `b : Γ(Y,T)` makes `c 0` exactly q^sharp.
- There is no assumption of freeness, normality, faithfulness, a field, or
  invertibility of the order of H.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  surjectivity uses the standard `AlgebraicGeometry.Surjective` instance argument.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow`, and the inherited
  scheme-module monoidal structure.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSection`, `tensorPullbackSectionAdjunction`,
  `tensorPullbackSectionComp`, `tensorPullbackSectionId`; `tensorPullback` and
  `pushforward` retain their existing constructions.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded independent-universe
  tensor interface, imported explicitly. The scheme-module tensor and
  `tmulSection` are the existing localization tensor and its pure-tensor map.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is the recorded general interface; `X.Modules` and `Y.Modules` use its
  existing `SheafOfModules` specialization, not a copied category.
- `Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil`: `pencilGroupElements`,
  `pencilTranslateTensor`, `pencilOrbitBundle`, from the added owning node.
- Proof imports include
  `Sheaf.AlgebraicGeometry.FiniteTrivializeInvertibleUpstairs`:
  `exists_trivialization_over_preimage_of_isFinite`, and
  `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`:
  `invertible_pullback_tensor`. The recorded symmetric structure
  `SheafOfModules.monoidalCategory` / `symmetricCategory` from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal` is also imported
  transitively by these modules. Its source and full signature were read.

Edge cases checked before and during writing: the empty scheme gives no local
points but all formulas still make sense; finite surjectivity forces Y empty
when X is empty. A group is nonempty, including the trivial group, whose orbit
bundle is L up to the normalized identity pullback and unitors. Repeated identical
factors in a nonfaithful action are retained. Fixed points and characteristics
dividing |H| cause no problem because only a fixed local frame and invariant
coefficients are used. Degree zero is the structure sheaf, including its full
scalar map. Tensor powers are indexed by all naturals, exactly the nonnegative
integers. The independent group universe v imposes no site-universe restriction.
No statement correction or STATEMENT-DISPUTED flag is necessary.

Searches for existing declarations:

- msearch leanfinder: "The tensor product of all translates of an invertible
  sheaf by a finite group descends through the invariant ring quotient";
  8 hits, all representation coinvariants or related representation formulas,
  including `Representation.Coinvariants.mk_inv_tmul`; no descent theorem.
- msearch loogle: `"Sheaf", "invariants"`; 0 hits.
- msearch grep in AlgebraicGeometry: `orbit.*[Tt]ensor|[Tt]ensor.*orbit|[Ll]ineariz`;
  0 hits. Broader project rg searches for `orbitTensor`, `linearization`,
  `linearisation`, invariant sheaves and norms found other action frameworks,
  not the requested descent theorem. Searching the item's exact identifier
  in `lean/WeilConjectures` found no declaration.
- msearch leansearch: "The tensor product of all translates of a line bundle
  under a finite group descends to an invertible sheaf on the invariant ring
  quotient"; 8 hits: `PiTensorProduct`, module invertibility under tensor,
  `CommRing.Pic.mk_tensor`, and representation coinvariants. None states this
  scheme-theoretic descent result.
- `tools/blueprint_refs.py search 'orbit tensor'`: 0 blueprint matches.
  DAG rg for orbit/tensor did find `def-sfb-pencil-orbit-bundle-norm` through
  its citers. I read its complete statement and lean record, obtained the
  server source, and reused its exact existing definitions, removing my draft
  duplicate orbit-list and orbit-bundle definitions before delivery.
- Exact-name rg of all project Lean and Mathlib found no existing declarations
  with the seven helper names or `orbit_tensor_line_descent`.

Validation uses only scompile.py and deliver2.py, against the live server build.
The first version exposed missing parentheses around `H → (X ≅ X)`; this was
fixed. The revision reusing the existing orbit bundle compiled, with one long
module-docstring line subsequently wrapped. The final dry run validates the
complete revised source and node record again.

## Second reading by Q119

I reopened the node and final module for a separate pass in this worker session;
the dispatcher explicitly prohibits starting other agents. Independent review
belongs to the maintainer after delivery.

I checked the action order against both the node's formula a_h a_g = a_(hg) and
the cocycle comparison, the equality transporting invariant inverse images,
and the normalization of the evaluation map under the recorded adjunction.
The inverse in `orbitQuotientPullbackIso` is on the pullback-composition
comparison, giving a_g^*q^*M → (q a_g)^*M → q^*M as required.
I checked each invariant-image equivalence has both directions and that each
inclusion is sectionwise injective. In particular, this entails an isomorphism
to the actual invariant sheaf, not just a morphism into it. The power map is
specified on arbitrary pure tensors, with a separate all-scalars degree-zero
formula, and not only on diagonal powers of sections. The diagonal orbit-frame
formulas for the linearizations determine those morphisms uniquely because
the imported finite-trivialization result provides generating frames locally.
The earlier duplicate orbit construction was removed after locating its owning
node; no second definition remains. No missing hypothesis or conclusion was
found in this pass.
