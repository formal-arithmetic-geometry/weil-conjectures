## Worker report

The module states `Scheme.separated_affine_functionField_surjective`. It binds an integral scheme `X`, its separatedness (`X.IsSeparated`), a nonempty affine open `U`, a point `x` outside `U`, Noetherianity and Krull dimension one of the stalk, and states surjectivity of the canonical algebra map from the tensor product of the affine sections and stalk to `X.functionField`. The `let` binders render A, B, K, and the map exactly; the proof is `sorry` as required.

Dependencies used: `AlgebraicGeometry.IsIntegral` (Mathlib.AlgebraicGeometry.Properties), `AlgebraicGeometry.Scheme.IsSeparated` (Mathlib.AlgebraicGeometry.Morphisms.Separated), `AlgebraicGeometry.IsAffineOpen` and `Scheme.Opens` (Mathlib), `Scheme.functionField` and `Scheme.germToFunctionField` (Mathlib.AlgebraicGeometry.FunctionField), `IsNoetherianRing` (Mathlib.RingTheory.Noetherian.Defs), and `ringKrullDim` (Mathlib.RingTheory.KrullDimension.Basic). The stalk/function-field inclusions are represented by `X.germToFunctionField U` and `algebraMap (X.presheaf.stalk x) X.functionField`.

Edge cases checked: U is explicitly nonempty; x is explicitly outside U; the universe is polymorphic and uses the standard `ULift ℤ` base only for the scheme's ambient separatedness convention; no positivity or nonzero assumptions are added. The tensor map is formed over ℤ via `RingHom.toIntAlgHom`.

Searches: `msearch.py leanfinder` for separated affine function-field tensor surjectivity (no exact declaration); `msearch.py loogle` for tensor/function-field declarations (only generic tensor and function-field APIs); `msearch.py grep` and `rg` over Mathlib and WeilConjectures (no matching theorem). No existing project declaration was found.

## Earlier second reading (a previous round; superseded)

The statement was independently checked against the DAG node. Every hypothesis (integrality, separatedness, affine nonempty open, point outside the open, Noetherian stalk, dimension one) and the conclusion (surjective canonical tensor map to the function field) is rendered by the corresponding binder or let expression. No mismatch was found.

## Second reading by E1

Read the node copy and the Lean file independently, together with every statement dependency's
statement and recorded Lean/Mathlib declarations. Read Stacks varieties.tex,
`lemma-find-globally-generated` (09NB), statement and opening proof paragraph, in the available
local source copy `/home/ubuntu/c1-stacks-review/varieties.tex`, lines 7855–7881 (the literature
path named by the node is not populated on this machine). The source introduces an integral
separated scheme, a nonempty affine open, and finitely many complementary points whose stalks
are Noetherian of dimension one. Its surjectivity argument is pointwise: the finite complement
is used later to choose one section for all points, not in the tensor-map argument. The node's
single-point formulation therefore has exactly the hypotheses needed for this extracted step;
no ground field, global Noetherianity, or global dimension assumption is implicit here.

Objects, hypotheses, and conclusion, item by item:

- Scheme X: `(X : Scheme.{u})`. This is Mathlib's scheme, the locally ringed space with local
  affine charts from def-pc-scheme. Exact.
- Integrality of X: `[IsIntegral X]`, from Mathlib.AlgebraicGeometry.Properties, the recorded
  declaration of def-pc-integral-scheme. Its nonemptiness and domain sections imply the source's
  reduced irreducible nonempty condition. Exact.
- Separatedness of X: `[hsep : X.IsSeparated]`. Read Scheme.IsSeparated and its
  `isSeparated_iff_isClosedImmersion_prod_lift` in Mathlib's Morphisms.Separated: this is
  separatedness over the terminal scheme, equivalently a closed absolute diagonal. It
  specializes the morphism notion AlgebraicGeometry.IsSeparated recorded by
  def-weil-proper-morphism; it does not assume properness or finite type. Exact.
- Nonempty affine open U = Spec A: `(U : X.Opens) (hU : IsAffineOpen U)
  [hUn : Nonempty U]` and `let A : Type u := Γ(X, U)`. Read IsAffineOpen in AffineScheme:
  it is IsAffine of the open subscheme. Thus its ring is canonically its sections; choosing
  this canonical affine presentation does not restrict an arbitrary Spec A presentation.
  Exact.
- Point outside U: `(x : X) (hx : x ∉ U)`. Quantified after U as in the node. Exact.
- Local ring B = O_{X,x}: `let B : Type u := X.presheaf.stalk x`. This is the structure-sheaf
  stalk, not a residue field or completed local ring. Exact.
- B Noetherian: `[IsNoetherianRing (X.presheaf.stalk x)]`. Read the recorded abbrev in
  Noetherian.Defs: every ideal finitely generated. No Noetherianity of X or A is imposed. Exact.
- B of Krull dimension one: `(hdim : ringKrullDim (X.presheaf.stalk x) = 1)`. Read the
  recorded definition in KrullDimension.Basic: supremum of strict prime-chain lengths in
  WithBot ℕ∞. Equality means exactly dimension one, not an upper bound. Exact.
- Function field K = k(X): `let K : Type u := X.functionField`. Read Mathlib.FunctionField:
  this is the stalk at genericPoint X and has its Field instance from IsIntegral. Also read
  the project's Sheaf.AlgebraicGeometry.FunctionField module recorded by def-sc-function-field:
  its component-product definition serves general curves, while its docstring explicitly
  assigns the arbitrary integral-scheme clause to Mathlib Scheme.functionField. Using that
  existing declaration here is the right specialization, with no duplicated notion. Exact.
- Inclusion A → K: `(X.germToFunctionField U).hom.toIntAlgHom`. Read the definition: germ at
  the generic point, which lies in U by nonemptiness. Mathlib's germToFunctionField_injective
  gives its injectivity, as required by lem-sc-integral-scheme-stalks-in-function-field. Exact.
- Inclusion B → K: `(algebraMap B K).toIntAlgHom`. Read stalkFunctionFieldAlgebra: the
  stalkSpecializes map from the generic point to x; the IsFractionRing stalk instance makes
  this injective and K the fraction field of B. This is the dependency's rho_x, with no
  arbitrary algebra structure supplied by the caller. Exact.
- Canonical ring map A ⊗_ℤ B → K: `let φ : TensorProduct ℤ A B →ₐ[ℤ] K :=
  Algebra.TensorProduct.lift ... (fun _ _ => Commute.all _ _)`. Read lift and toIntAlgHom:
  the map sends a pure tensor to the product of the two canonical inclusions. A ℤ-algebra
  homomorphism is just the corresponding unital ring map with its canonical integer action;
  no extra compatibility hypothesis is imposed. Exact.
- Surjectivity, the whole conclusion: `Function.Surjective φ`. Every element of K has a
  preimage in this tensor product; neither an injectivity nor a bijectivity assertion is added.
  Exact.

Edge cases: the empty scheme is already excluded by integrality; an empty U is expressly
excluded in both node and Lean. U = X has no admissible x and hence no assertion to apply.
The zero stalk and dimension-zero stalk are excluded by the exact original dimension-one
hypothesis and integral domain property, not by new binders. No finite complement, index set,
or integer n is bound in this pointwise lemma. Arbitrary characteristic is allowed, including
mixed characteristic, because the tensor base is ℤ, not a field. Explicit `universe u` and
Scheme.{u} cover every scheme universe; section rings, stalks, and the function field share
that universe canonically. Every binder is bound explicitly. All hypotheses remain in the
same order, and the lets only abbreviate existing objects.

Independent searches (2026-10-11):

- `msearch.py ... leanfinder "The products of sections on an affine open and germs at a point
  generate the rational function field of a separated integral scheme"`: eight hits including
  Scheme.functionField, Scheme.germToFunctionField, functionField_isFractionRing_of_isAffineOpen,
  and the stalk IsFractionRing instance; none states tensor-map surjectivity.
- `msearch.py ... loogle "Algebra.TensorProduct.lift"`: twelve hits, the universal tensor-map
  construction and its identities; no scheme-specific surjectivity theorem.
- `msearch.py ... leansearch "For a separated integral scheme the tensor product of affine
  open sections and a dimension one local ring surjects onto the function field"`: unavailable
  (Internal Server Error). No absence verdict inferred from this failed service.
- `msearch.py ... grep "functionField.*surject|surject.*functionField|tensor.*germToFunctionField"`:
  zero hits. Independent rg over Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  with that pattern plus the proposed declaration name found only unrelated upstream stalk
  comparison surjectivity and SerreDuality fraction-field uses. Additional searches
  `tensor.*(fraction|rational)|surject.*(generic|stalk)|separated.*(tensor|fraction)` over the
  project's and upstream algebraic geometry modules found general sheaf/stalk results, not
  this theorem. No existing declaration with the node's statement was found.

Mismatch and repair: H8, the theorem docstring omitted all three proof steps. Added the
canonical local scheme and principal localization argument identifying the fiber product
with Spec K; the base change of the closed diagonal; and the affine closed-immersion
surjectivity criterion, with each supporting node named. H9, added the project's copyright
header, replaced the unused Proper import with Separated, and removed unrelated tensor
opposite, ring-category constructions, and redundant Properties imports. Imported
RingTheory.TensorProduct.Maps directly for lift; removed unused namespace opens. The theorem
signature and the node's Lean record were unchanged and checked verbatim equal. No
mathematical mismatch, node correction, new definition node, or dependency module was needed.
The sole theorem still has proof `sorry`; there are no definitions or proved helper lemmas.
Every declaration and the module docstring have the source and blueprint marker.

Validation: `scompile.py E1 lem-sc-separated-affine-function-field-surjective` on the revised
module passed (1.8 seconds), with no errors or warnings. All lines are at most 100 characters.
