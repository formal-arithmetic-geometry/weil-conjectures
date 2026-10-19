## Worker report

The module `lean/Sheaf/ZetaWeil/PerfectPairingLineEquivariance.lean` states
`LinearMap.perfectPairingLineEquivariance`. It uses the same objects as the node:
`L` is a field; `V`, `W`, and `M` are finite-dimensional `L`-vector spaces;
`β : V →ₗ[L] W →ₗ[L] M` is the bilinear pairing; and `F_V`, `F_W`, and `F_M`
are linear endomorphisms. The two perfectness clauses are rendered by
`Function.Bijective β` and `Function.Bijective β.flip`, respectively. Since `β`
is a nested `LinearMap`, `β.flip` is the induced map `W →ₗ[L] V →ₗ[L] M`.

The hypotheses and clauses are rendered as follows.

* “`V`, `W`, and `M` are finite-dimensional `L`-vector spaces” is
  `[AddCommGroup V] [Module L V] [FiniteDimensional L V]`, and the corresponding
  binders for `W` and `M`.
* “`β` is `L`-bilinear” is `β : V →ₗ[L] W →ₗ[L] M`.
* Perfectness in the first variable is `hβ : Function.Bijective β`; perfectness
  in the second variable is `hβ_flip : Function.Bijective β.flip`.
* The endomorphisms are the binders `F_V : V →ₗ[L] V`, `F_W : W →ₗ[L] W`, and
  `F_M : M →ₗ[L] M`.
* The compatibility equation for every `x : V` and `y : W` is
  `hcompat : ∀ (x : V) (y : W), β (F_V x) (F_W y) = F_M (β x y)`.
* `F_V = id_V` and `F_M = c · id_M` are `hV : F_V = LinearMap.id` and
  `hM : F_M = c • LinearMap.id`, with `c : L`.
* The hypotheses `dim_L V = 1` and `dim_L M = 1` are
  `hVdim : Module.finrank L V = 1` and `hMdim : Module.finrank L M = 1`.
* The conclusion `dim_L W = 1` is `Module.finrank L W = 1`.
* For every nonzero `e : V`, the evaluation map `β(e,-)` is already an
  `L`-linear map (`β e : W →ₗ[L] M`), and its being a linear isomorphism is
  rendered by `Function.Bijective (β e)`. Its equivariance clause is
  `∀ y : W, β e (F_W y) = F_M (β e y)`.
* The final scalar-action clause is `F_W = c • LinearMap.id`.

The statement proof is `sorry`, as required for stage 2. The declaration docstring
records the six proof steps from the node: choosing a nonzero vector in `V`, proving
evaluation injective via the flipped pairing, proving surjectivity via the pairing,
obtaining the singleton basis and dimension of `W`, substituting in the compatibility
identity for equivariance, and cancelling the evaluation map to obtain the scalar
endomorphism.

The dependency `def-weil-finite-dimensional-subspace` is rendered by Mathlib's
`FiniteDimensional` class (the node records that as its `mathlib_match`), so no
project declaration is imported. The dimension dependency
`def-weil-vector-space-dimension` is rendered by `Module.finrank` from
`Mathlib.LinearAlgebra.Dimension.Finrank`.

Edge cases checked: the hypotheses force `V` and `M` to be nonzero because their
finrank is one, so the universal nonzero-`e` clause is non-vacuous; `W = 0` is
incompatible with perfectness and the dimension conclusion; the statement permits
`c = 0` and does not divide by `c`; arbitrary fields, including characteristic two,
are allowed; and the dimensions and modules have independent explicit universes.

Searches for an existing declaration were made with the required tools. LeanFinder
(`perfect bilinear pairing line equivariance vector spaces` and `A bilinear form
perfect in both variables and valued in a line induces an isomorphism by fixing a
nonzero vector in a one dimensional factor; if the first operator is identity then
the second operator equals the target scalar`) returned only Mathlib perfect-pairing
building blocks (`LinearMap.IsPerfPair`, `LinearMap.toPerfPair`, and related
lemmas), not this line-valued equivariance statement. Loogle
(`LinearMap.IsPerfPair, Module.finrank`) returned `Module.finrank_of_isPerfPair`
and related dimension lemmas only. LeanSearch (`Evaluation at a nonzero vector in
a one dimensional vector space is a linear isomorphism of Hom(V,M) to M`) returned
evaluation-map primitives only. The required grep search for
`IsPerfPair|finrank_eq_one|exists_smul_eq_of_finrank_eq_one` found Mathlib's
perfect-pairing and one-dimensional linear algebra declarations, but no complete
match. `rg` over `WeilConjectures/` and the project `lean/Sheaf` found no declaration
for this node; the only nearby source result is the scalar-valued similitude theory
in `WeilConjectures/ZetaLinearAlgebra/Pairing.lean`, which does not state the
line-valued evaluation and `c = 0` result. No statement correction or
`STATEMENT-DISPUTED` flag is needed.

## Second reading by Q30

I reread the node and the module signature independently. The field, three vector
spaces, finite-dimensional hypotheses, bilinear pairing, both bijectivity clauses,
three endomorphisms, compatibility equation, identity/scalar normalizations, and
the two one-dimensional hypotheses all occur as explicit Lean binders. The three
conclusion clauses match in order: `finrank W = 1`; for each nonzero `e`, the
linear evaluation map is bijective and satisfies the pointwise equivariance
identity; and `F_W` is scalar multiplication by `c`. `β.flip` is exactly the
second induced map from `W` to `Hom_L(V,M)`, and no scalar-valued or extra
nonzero-`c` assumption was introduced. The file compiles cleanly with only the
expected `sorry` warning.
