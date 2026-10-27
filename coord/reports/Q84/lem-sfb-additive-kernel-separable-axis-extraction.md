## Worker report

The module `Sheaf.AlgebraicGeometry.AdditiveKernelSeparableAxisExtraction` states
`AlgebraicGeometry.additive_kernel_separable_axis_extraction`, with one `sorry` and no new
definitions. The item's JSON changes only its `lean` field. No statement correction or new
node is needed. The source was read at
https://math.stanford.edu/~conrad/papers/appbnew.pdf, Lemmas 1.11--1.13, printed pp.6--7.
The proof docstring carries all five steps of the node's proof, including the one-dimensional
degree argument and the scheme-theoretic, rather than rational-point-only, conclusion.

Hypotheses and clauses, in order:

- The ground field is `{k : Type u} [Field k]`. Prime positive characteristic is
  `(p : ℕ) [Fact p.Prime] [CharP k p]`; primality includes positivity.
- Every positive dimension is written uniquely as `n + 1`, with `(n : ℕ)`. Thus the node's
  E is `∏ᶜ (fun _ : Fin (n + 1) ↦ Grp.mk (StandardGroupSchemes.additive k))`.
  This is the categorical product of the recorded additive group, including its group law.
  Its underlying object is `.X : Over (Spec (.of k))`. This parameter change excludes no
  positive dimension and adds none. The target projection retains coordinates 1 through n.
- The input `f` is a morphism from this product to `Grp.mk (StandardGroupSchemes.additive k)`
  in `Grp (Over (Spec (.of k)))`, so it is a k-group-scheme homomorphism, not an arbitrary
  scheme map. Its underlying map over k is `f.hom.hom`.
- The separable closure is `(K : Type u) [Field K] [Algebra k K]`,
  `[Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K] [IsSepClosed K]`.
  All algebraic separable closures admit a small model in the universe of k. No finite,
  perfect, or algebraically closed hypothesis is imposed.
- `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))` is actual scalar extension
  along Spec K -> Spec k. The object in the type of `u` is exactly E_K.
- `StandardGroupSchemes.additive K` is Spec K[t], with its structure map over K. The map
  `u` is a morphism in `Over (Spec (.of K))` from this affine line to E_K. No group
  homomorphism assumption is imposed on u.
- `hu` says u does not factor through a K-point: there is no map `c` from the tensor unit
  Spec K for which `toUnit (StandardGroupSchemes.additive K) ≫ c = u`. For this affine
  source and affine target this is exactly nonconstancy of the polynomial coordinate tuple.
  In particular it is not a condition only on the finite set of rational points.
- `hfu` says `u ≫ (Over.pullback ...).map f.hom.hom` equals the same composite with the
  constant-zero map `1 : E.X ⟶ StandardGroupSchemes.additive k` in place of f. Here the
  multiplicative notation `1` is Mathlib's identity element in the group of maps into a
  group object, hence additive zero for Ga. Base change preserves this constant map, so
  this is precisely f_K composed with u equals zero. This formulation does not require
  choosing a second group structure on the base-changed object.
- The existential `α` is an isomorphism in the category of group schemes from E to itself.
  It therefore includes inverse scheme maps and compatibility with the group law, allowing
  nonlinear additive-polynomial automorphisms.
- The existential `g` is a group-scheme homomorphism from the product indexed by `Fin n`
  to Ga. `Pi.map' Fin.succ (fun _ ↦ 𝟙 ...)` is the specified projection onto the last n
  coordinates. `α.hom ≫ f = ... ≫ g` is f composed with α equals g composed with π,
  with Lean's left-to-right composition convention.
- The first axis is `Pi.lift (fun i : Fin (n + 1) ↦ if i = 0 then 𝟙 ... else 0)`.
  This is the group map t -> (t,0,...,0); zeros here are categorical zero group maps.
  The existential group morphism `l` lands in `Grp.mk (GrpObj.ker f.hom.hom)`. The equality
  `l.hom.hom ≫ GrpObj.kerι f.hom.hom = axis.hom.hom ≫ α.hom.hom.hom` states the required
  scheme-theoretic subgroup containment. The kernel is the fibre product over the zero
  section by its recorded definition, not just a kernel on k-points. A factorization of
  this mono through the kernel is also a mono, so the image is a subgroup scheme.
- Finally `(n = 0 → f = 0)` states exactly the node's dimension-one conclusion.
  In that case the target of π is the empty product, Spec k.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs. Its nontriviality and inversion
  data are the recorded field notion.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.additive`, `.additiveGroup`,
  `.affine`, `.additiveComul`, `.additiveCounit`, `.additiveAntipode` and
  `.additiveGroup_existsUnique`, in Sheaf.AlgebraicGeometry.StandardGroupSchemes. The
  comultiplication is y -> y tensor 1 + 1 tensor y; the counit is evaluation at zero.
  The module supplies the exact recorded Ga rather than a private polynomial/Hopf model.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `Grp`, `Grp.mk`, `IsMonHom`, and the
  underlying morphism accessors, in Mathlib.CategoryTheory.Monoidal.Grp and Mon;
  `CategoryTheory.Hom.group` in Mathlib.CategoryTheory.Monoidal.Cartesian.Grp;
  `CategoryTheory.GrpObj.ker`, `.kerι`, `.instGrpObjKer` in
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, publicly available through
  the recorded group-scheme interface. Their full signatures and relevant docstrings were
  read. The kernel is explicitly `pullback f η[H]`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in
  Mathlib.AlgebraicGeometry.Scheme, publicly imported through StandardGroupSchemes.
- `def-weil-polynomial-ring`: `Polynomial` in Mathlib.Algebra.Polynomial.Basic, used in the
  recorded Ga = Spec K[t], not reimplemented.
- Finite group-object products and their group structures come from
  Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits; `Pi.map'`, `Pi.lift`, `Pi.π` are
  Mathlib.CategoryTheory.Limits.Shapes.Products. Base change is `CategoryTheory.Over.pullback`
  in Mathlib.CategoryTheory.Comma.Over.Pullback. The separable-closure predicates are
  Mathlib.FieldTheory.IsSepClosed and its public imports.
- Available proof dependencies are imported privately: Mathlib.Algebra.MvPolynomial.Basic
  (`MvPolynomial`, `def-weil-pbc-mv-polynomial-ring`) and
  WeilConjectures.Mathlib.Algebra.CharP.Lemmas (`iterateFrobeniusOfPrime`,
  `def-weil-ring-frobenius`). The two proof-only nodes
  `lem-trf-additive-polynomial-monomial-classification` and
  `lem-sfb-diagonal-p-form-separable-isotropy-descent` have no recorded Lean declaration;
  no fictitious imports or new theorem statements were added for them. All other proof
  dependencies are already among the public statement imports.

Edge cases checked before drafting and again against the final signature:

- Dimension one is `n=0`, with nonempty domain `Fin 1`, empty last-coordinate product,
  and the explicit f=0 conclusion. There is no accidental assumption `0 < n` on the tail.
- Zero f admits the identity automorphism and zero g; the axis factors through its full
  kernel. No nonzero or surjective assumption on f is present.
- Constant nonzero curves, and the zero curve, fail hu as intended. A polynomial such as
  t^p-t over a finite field is still nonconstant despite vanishing on rational points;
  the morphism-factorization definition of hu correctly detects that.
- The curve need not pass through zero, since its constant coordinates are allowed;
  the proof uses the positive-degree leading coefficients.
- Imperfect k and p=2 are included. No extraction of p-th roots or linearity hypothesis
  occurs. The proof uses only invertible additive coordinate substitutions.
- The first-axis factorization is an equality of scheme morphisms through the actual
  pullback kernel, so it holds on nonreduced test algebras as well as on fields.
- k can already be separably closed and K=k with its identity algebra; no strictness or
  finite-degree assumption is imposed. Empty affine line and zero-field cases do not
  arise because K is a field.

Searches performed for existing declarations:

- `msearch.py ... leanfinder`: "A homomorphism of additive group schemes from Ga power n
  to Ga whose kernel contains a nonconstant affine line over a separable closure becomes
  independent of one coordinate after a group automorphism". Eight hits, including
  `AffineSpace.homOverEquiv_apply`, `AffineSpace.reindex`, and Ax--Grothendieck statements.
  These provide coordinate descriptions or unrelated injectivity results, not extraction.
- `msearch.py ... loogle "MvPolynomial, AlgEquiv"`: twelve hits including
  `MvPolynomial.renameEquiv`, `uniqueAlgEquiv`, `optionEquivRight`, `mapAlgEquiv` and their
  formulas. None states the nonlinear additive-kernel theorem.
- `msearch.py ... grep "vectorGroup|additivePower|coordinate.*automorphism" AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch`: "An additive group scheme homomorphism with a nonconstant
  polynomial curve in its kernel over a separable closure admits a group automorphism
  extracting a coordinate axis". Eight hits, including `AddMonoidHom.ker`,
  `AddMonoidHom.fiberEquivKer`, and `Scheme.Hom.ker`; none is this group-scheme theorem.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry` for
  `vectorGroup|additivePower|additiveGroup|nonconstant|Nonconstant`, and for
  `additive polynomial|coordinate.*automorphism|vector group`. Found the recorded
  StandardGroupSchemes module and CharZeroCommutativeUnipotentVectorGroup, which confirms
  the shared categorical-product encoding but has characteristic zero and a different
  theorem. No positive-characteristic extraction statement exists there.
- Recursive search of `lean/WeilConjectures` for the item id returned no match.
  Search of Mathlib, upstream, Sheaf and `dag/lean_names_upstream.json` for the full new
  declaration's last component `additive_kernel_separable_axis_extraction` found no clash.

Validation: `scompile.py Q84 lem-sfb-additive-kernel-separable-axis-extraction <module>`
passed in sandbox and library modes, in 6.5 s and 11.5 s respectively, with no errors or
unexpected warnings. No local compiler, global build, live source write, or direct Git
command was used. The dry run and delivery are recorded below after completion.

## Second reading by Q84

Reopened the node and the completed Lean signature for a second clause-by-clause pass.
This was a self-review by the dispatcher worker, in accordance with the instruction not
to start other agents; the maintainer performs the independent delivery review.

Checked the dimension shift, all three separable-closure conditions, the actual pullback
E_K, the unrestricted scheme morphism u, nonfactorization through a K-point, and equality
with the base-changed constant-zero map. Checked that α, f, g and l are morphisms in the
group-object category, that `Fin.succ` drops exactly the first coordinate, and that the
axis lift is identity only at index zero and zero elsewhere. Checked the orientation of
both composition equalities: α then f, π then g; l then kernel inclusion, axis then α.
The kernel is the zero-section fibre, not a pointwise set. Checked that n=0 is retained
and says f=0. All binders and the universe are explicit, all definitions used are existing
ones, and the only new theorem proof is `sorry`. No mismatch was found and no node clause
was changed.

The prescribed `deliver2.py ... --no-push` finished successfully: commit `a24b1dddaf8`
passed the server preflight and per-file compilation (`OK (dry run)`); nothing was pushed
by that validation. The only subsequent change is this validation note.
