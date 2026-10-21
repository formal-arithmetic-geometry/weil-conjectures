## Worker report

This is an `existing: true` delivery. No Lean module or new declarations are needed.
The exact existing source is
`lean/WeilConjectures/CategoryTheory/ModuleObjects/Bimod.lean`, module
`WeilConjectures.CategoryTheory.ModuleObjects.Bimod`. I read the entire module locally
and independently fetched its current live-server text with
`scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.Bimod`; the relevant
interfaces and bodies agree. The source blueprint is
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-module-category/lem-sfb-modobj-symmetric-bimodules.md`.
The node's statement, dependencies and proof remain unchanged; only `lean` is added.

The record names all five declarations needed for the complete statement:

- `CategoryTheory.Mod.toBimodObj` (line 55), signature
  `def toBimodObj (M : Mod C R) : Bimod (Mon.mk R) (Mon.mk R)`.
- `CategoryTheory.Mod.toBimod` (line 81), signature
  `def toBimod : Mod C R ⥤ Bimod (Mon.mk R) (Mon.mk R)`.
- `CategoryTheory.Mod.fullyFaithfulToBimod` (line 94), signature
  `def fullyFaithfulToBimod : (toBimod R : Mod C R ⥤ _).FullyFaithful`.
- `Bimod.IsSymmetric` (line 141), signature
  `def IsSymmetric (P : Bimod A A) : Prop`.
- `Bimod.isSymmetric_toBimodObj` (line 167), signature
  `lemma isSymmetric_toBimodObj (M : Mod C R) : (Mod.toBimodObj R M).IsSymmetric`.

The main signature in `lean.statement` is copied verbatim from the existing definition,
ending immediately before `where`. Its surrounding binders are detailed below.

Hypotheses and clauses:

1. A braided monoidal category is rendered by `{C : Type u} [Category.{v} C]
   [MonoidalCategory C] [BraidedCategory C]`. Universes `u` and `v` are independent;
   the braiding is Mathlib's `β_`. There is no `SymmetricCategory` assumption.
2. The commutative monoid object is `{R : C} [MonObj R] [IsCommMonObj R]`.
   `Mon.mk R` bundles exactly this monoid object, without introducing a different ring.
3. An arbitrary left module is `(M : Mod C R)`, using the dependency's recorded
   `CategoryTheory.Mod` with ambient action category instantiated as `C` itself.
4. The object and left action in `toBimodObj` are literally `X := M.X` and
   `actLeft := γ[R,M.X]`. Its right action is literally
   `actRight := (β_ M.X R).hom ≫ γ[R,M.X]`.
   Lean's diagrammatic composition is exactly the ordinary composite in the node.
5. The conclusion that these actions form a bimodule is the return type
   `Bimod (Mon.mk R) (Mon.mk R)` together with the five structure fields:
   `one_actLeft`, `left_assoc`, `actRight_one`, `right_assoc`, `middle_assoc`.
   The right-associativity field uses the inverse associator, equivalently the
   displayed node equation after precomposition with the associator.
6. Symmetry is exactly `P.actRight = (β_ P.X A.X).hom ≫ P.actLeft`, the body of
   `Bimod.IsSymmetric`; it imposes no condition that the braiding itself be symmetric.
7. The stated functor is `toBimod R`: its object map is `toBimodObj R`, and its
   morphism map has `hom := f.hom`. The two morphism equations are the left-module
   morphism equation and its consequence under naturality of the braiding.
8. Full faithfulness is the `Functor.FullyFaithful` structure returned by
   `fullyFaithfulToBimod`. Its preimage is `Hom.mk' f.hom f.left_act_hom`, exactly
   the inverse operation on hom-sets described by proof step 5, and it keeps the
   underlying map. This supplies a specified hom-set inverse, not a bare existence.
9. Every functor value is symmetric by `Bimod.isSymmetric_toBimodObj M`.
   Its proof is `rfl`, since the right action was defined by this formula.

Dependency declarations read and used by the existing implementation:

- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`, `Mod.Hom.mk'`, the category instance,
  `Mod.regular` and `Mod.forget`. The signatures and docstrings were read in Mathlib.
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod` imports that exact module
  and provides the tensor-specialized `CategoryTheory.Mod.act`, `one_act`,
  `mul_act`, `act_hom`; these are used by the existing construction.
- `det-def-sfb-ring-object-monoid`: its `mathlib_match` in
  `Mathlib.CategoryTheory.Monoidal.Mon`: `CategoryTheory.MonObj`, `Mon`,
  `IsMonHom`, `Mon.Hom`, `Mon.id`, `Mon.comp`, the category/faithful forgetful
  functor, and `IsCommMonObj`. In particular the latter's field says
  `(β_ R R).hom ≫ μ = μ`, exactly the required commutativity.
- `def-sfb-bimod-objects`: its `mathlib_match` in
  `Mathlib.CategoryTheory.Monoidal.Bimod`: root-level `Bimod`, `Bimod.Hom`,
  `Bimod.instCategory`, `Bimod.hom_ext`. I read the full five-law structure and both
  morphism compatibility equations.
- Proof dependencies `lem-sfb-braiding-hexagon`, `lem-sfb-braiding-naturality`,
  `lem-sfb-braiding-unitors`: their exact Mathlib declarations in
  `Mathlib.CategoryTheory.Monoidal.Braided.Basic` are
  `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`,
  `braiding_tensor_right_hom`, `braiding_naturality`, and
  `CategoryTheory.braiding_leftUnitor`. Their full signatures were read.
  The existing module imports these modules and uses those formulas.

Proof alignment: `toBimodObj` inherits the two left laws (node step 1), proves the
right unit law with naturality and `braiding_leftUnitor` (step 2), and proves right
associativity and compatibility with the hexagons and commutativity (steps 3–4).
The auxiliary `Mod.braiding_whiskerRight_smul` is the use of commutativity in
these calculations. `toBimod` and `fullyFaithfulToBimod` implement step 5.
All relevant construction data and proofs are already present upstream. This delivery
introduces no definitions, postponed theorems or additional axioms.

Edge cases checked by reading the actual binders and bodies: a braided category whose
braiding is not symmetric is admitted; no coequalizers, tensor-colimit preservation,
additivity, abelianness, sheaf hypotheses, nonzero objects or inhabitedness are assumed.
The zero monoid/module in any additive example is included. Arbitrary object and
morphism universes are retained. The tensor-unit monoid is included. There is no
claim that every bimodule is symmetric or that this functor is essentially surjective.
The coequalizer assumptions later in the file belong only to the tensor-product lemma;
the section ends before `isSymmetric_toBimodObj`, so they do not constrain this node.

Searches run with the prescribed `msearch.py Q149 lem-sfb-modobj-symmetric-bimodules`:

- `leanfinder "module objects over a commutative monoid in a braided monoidal category give symmetric bimodules and a fully faithful functor"`:
  eight hits, including ModuleCat symmetric-category instances and regular module
  objects; none expresses this generic module-to-bimodule functor.
- `loogle "CategoryTheory.Mod, Bimod"`: OK, zero hits.
- `grep "toBimod|fullyFaithfulToBimod|IsSymmetric|symmetricBimod" CategoryTheory/Monoidal`:
  OK, zero Mathlib hits.
- `leansearch "fully faithful functor from internal left modules over a commutative monoid object to bimodules with right action given by braiding"`:
  eight hits, including `CommMon.fullyFaithfulForget₂Mon` and braided-category
  transport results; none is this statement.
- Local `rg` for `symmetric[Bb]imod|fullyFaithfulToBimod|toBimod|[Ii]sSymmetric`
  in `lean/WeilConjectures` and `lean/Sheaf`, and the upstream-name index, found
  the exact upstream module above and its consumers. The Sheaf hits are consumers
  or unrelated symmetric-algebra predicates, not another implementation.
- `grep -rn 'lem-sfb-modobj-symmetric-bimodules' lean/WeilConjectures` returned no
  node-id annotation; searching the declaration names nevertheless found the exact match.
- DAG searches for `fullyFaithfulToBimod`, `isSymmetric_toBimodObj`, `toBimodObj`
  and `IsSymmetric` found this node's blueprint name and related searches, not an
  already attached duplicate statement. No new node is required.

No statement fault, statement correction or `STATEMENT-DISPUTED` issue was found.
Since this delivery records only existing declarations and contains no Lean file,
there is no delivered file to compile; the prescribed dry-run checks the existing
binding on the server. The live-server source retrieval succeeded.

## Second reading by Q149

I reread the node, its source blueprint, and the full existing upstream module after
preparing the binding. This is a same-worker rereading: the dispatcher's explicit
instruction forbids starting other agents; the maintainer supplies the independent
review. No independent-agent reading is claimed here.

The category, braiding and commutative monoid binders match without extra assumptions;
the Mathlib `Mod C R` is the same recorded left-module category. The object field,
left action and displayed braiding-then-left-action agree literally with the node.
The bimodule return type supplies all five laws; the functor keeps underlying maps;
the fully faithful structure supplies inverse hom maps. `Bimod.IsSymmetric` is the
node's exact definition and `isSymmetric_toBimodObj` proves its final universal clause.
I specifically checked that the later coequalizer/tensor-preservation section has
closed before that lemma, and that no symmetric-braiding assumption is present.
No mismatch was found and no source or DAG statement needed changing.

Validation: `deliver2.py Q149 lem-sfb-modobj-symmetric-bimodules --no-push`
returned `OK (dry run)` on 2026-10-21. The wrapper compiled its generated existing-binding
probe (`Sheaf.Stage2.Sandbox0` and `Sheaf.Stage2.Check`) and passed server preflight;
no Lean source file is part of the delivery.
