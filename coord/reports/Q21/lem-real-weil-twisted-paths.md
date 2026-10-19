## Worker report

This delivery states `AlgebraicGeometry.Scheme.FiniteEtale.weilTwistedPaths` in
`Sheaf.AlgebraicGeometry.FundamentalGroup.WeilTwistedPaths`. Only its proof is `sorry`.
The seven helper declarations give the pairs, their componentwise conditions, and explicit
composites of existing canonical maps. They belong to the twisted-path notion introduced by
this statement, rather than introducing independent mathematical notions. No definition chooses
data from an existence theorem. No statement is changed and there are no additional DAG nodes.

The previous worker called the assignment stale because Q09 had merged it. I opened Q09's
report and the node: that was a stage-1 split with nine proof steps and no Lean record.
It did not already discharge this stage-2 item.

Hypothesis and clause correspondence:

- The fixed finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`. Its base and
  arbitrary fixed closure are `D.k₀` and `D.k`; the cardinality is `D.q`. Its prime, positive
  exponent, base cardinality, algebra structure and algebraic closure are fields of that
  recorded definition, not extra assumptions here.
- The scheme over the base field is `X₀ : Over (Spec (.of D.k₀))`.
  `GeometricallyConnected X₀.hom`, `IsSeparated X₀.hom`, `LocallyOfFiniteType X₀.hom` and
  `QuasiCompact X₀.hom` render exactly geometric connectedness, separatedness and finite type.
- `D.geometricFiber X₀` is the recorded fibre product with the fixed closure. The projection
  `Limits.pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))` is its map to X₀.
- The geometric basepoint is `b : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left`, with explicit
  `Ω : Type u`, `Field Ω` and `IsAlgClosed Ω`. It is not restricted to a rational point of X.
- `D.geometricFrobenius X₀` is precisely the recorded automorphism id × Spec(γ), not the
  relative or absolute Frobenius. The integer exponents are `^ n` for `n : ℤ`.
- `fiber` is the existing finite-étale fibre functor. Paths are actual natural isomorphisms
  `fiber a ≅ fiber b`; naturality includes all cover morphisms.
- `TwistedEtaleLoop g b` is the full dependent pair type
  `Σ n : ℤ, fiber b ≅ fiber (b ≫ (g ^ n).hom)`.
- The existential `G : Group (TwistedEtaleLoop ... b)` asserts a group structure on exactly
  these pairs. `IsTwistedEtaleLoopMultiplication ... G.mul` specifies its degree sum and the
  displayed path product. Its argument `y` is the unique lift of `q(z)` to the pulled-back
  cover, as determined by `pullbackFiberIso`. The right side applies `p` at that cover, then
  projects to P. Thus it is `g^m(p) ∘ q`, in the stated order, for every P and every z.
  The comparison is a bijection, so this universal condition does not lose a clause through
  a nonexistent lift. It also avoids endpoint casts after addition of integer degrees.
- `E` is an equivalence of the full pair type with the recorded `weilGroup`, and
  `∀ p q, E (G.mul p q) = E p * E q` makes it a group isomorphism for G. Its codomain uses
  the actual arithmetic group `Aut (fiber (b ≫ π))`, as the node stipulates.
- `IsWeilTwistedPathIdentification` equates `(E p).val.2.toAdd` with `p.1`, and specifies
  every component of `(E p).val.1` on every arithmetic cover P₀. A geometric lift z of the
  pullback first maps to its arithmetic lift by `pullbackFiberIso`; on the right it first
  follows p then projects to P₀. This is the node's canonical endpoint identification.
  The coordinate `.val.2.toAdd` is definitionally the integer value of `weilGroupDeg`.
- The `∀ E'` conjunct says that those degree and arithmetic-cover component conditions
  characterize E uniquely; E' is not assumed to satisfy the group or closed-point clauses.
- The degree-zero conjunct takes a pair p of degree zero and the corresponding
  `h : Aut (fiber b)`, identified componentwise on underlying lifts, and asserts
  `(E p).val.1 = fiberAutBaseChange π b h`. This is exactly the recorded canonical geometric
  subgroup inclusion, not an independently chosen homomorphism. Pointwise equality of lifts
  is the same as equality of fibre maps (`fiber_ext`); it handles the g^0 endpoint cast.
- `HasWeilTwistedClosedPointFormula` universally takes a closed point x, an integer degree
  written as `e : ℕ` with `Nat.card (X₀.left.residueField x) = D.q ^ e`, an embedding ι of
  its residue field in D.k, and its lift a. For a finite-type scheme over a finite field,
  the residue field of a closed point is finite; its cardinality q^e is equivalent to
  `[κ(x):k₀] = e`. Since q > 1 this e is unique and positive. This is an encoding of the
  given degree, not an extra restriction or a claim about arbitrary nonclosed points.
- The two equations on a are respectively the residue embedding followed by the canonical
  residue point, and scalar coordinate id. The fibre-product condition then implies that ι
  commutes with k₀, so these parameters are exactly a chosen k₀-embedding and its lift.
  Every such embedding has this unique lift by the pullback universal property.
- Its first conclusion is `a ≫ (g ^ e).hom = (twistedPathSpecFrobenius D ^ e).hom ≫ a`,
  rendering `g^e a = a Spec(γ^e)` in Lean's composition convention.
- It asserts existence of the natural return path c and on every cover the equality
  `(c.hom.app P z).left = Spec(γ^e) ≫ z.left`. The helper `twistedPathSpecFrobenius` uses
  the recorded field geometric Frobenius (inverse q-power map), via `specMapIso`, for the
  arbitrary fixed closure D.k.
- For every `τ : fiber a ≅ fiber b`, the existential τe is characterized on all pulled-back
  covers by `IsTwistedEtalePathTranslate ... e τ τe`; hence it is exactly g^e(τ).
  The input to E is literally `⟨e, τ.symm ≪≫ c ≪≫ τe⟩`, the path in the node.
- The proof object hfix asserts that Spec(γ^e) fixes the arithmetic geometric point a₀.
  `fiberPrecompIso a₀ (Spec(γ^e)) hfix` is the existing natural automorphism obtained by
  residue-field reparametrization. Its conjugate by `restrictTwistedEtalePath π τ` is the
  decomposition-group image defined by τ, on every arithmetic cover. The equality with
  `(E ...).val.1` asserts exactly the specified image of geometric Frobenius of κ(x).
  The final degree equality is explicitly e. No sheaf Frobenius operator is asserted.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and `.geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`, built from `galoisMap`; I read its
  inverse and projection docstrings too. They retain the arbitrary fixed closure.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`:
  `AlgebraicGeometry.Scheme.FiniteEtale.fiber`, `fiber_ext` and the lifted-point description.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`: `weilGroup`,
  `weilGroupDeg`, `constantCover`, `constantCoverAction` and `geometricFrobenius`; the defining
  signatures and docstrings show the constant-cover normalization and degree convention.
- The scheme-conventions dependency is explicitly a convention record with no declaration.
  Its meanings are used as the Mathlib scheme properties, not restated in a dependency module.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality`: `pullback`,
  `fiberPrecompIso`, `specMapIso`; its currently split-out
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction` defines `pullbackFiberIso`.
  The declarations and their full signatures were read in those source modules.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport`: the canonical
  `fiberAutBaseChange` and proof dependency `finiteEtaleWeilTransport`. Its full statement
  and natural-language construction were read. The former is used directly for degree zero.
- Proof imports include `WeilConjectures.GroupTheory.WeilGroup` (`exact_weilGroupDeg`),
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` (finite étale algebra criterion) and
  `Mathlib.FieldTheory.Finite.GaloisField` (finite-field Galois theorem). The other existing
  proof interfaces arrive through the public dependency imports. The arithmetic-lift path
  node has no Lean record at present; no fictitious import is added for it.

Sources checked: the actual statements of Stacks 0BN5, 0BND and 0BTX in `pione.tex`, the
current main-20261015 unit proof `p-real-operations.proof.md`, Q09's report and reviewed node,
and Deligne Weil II pp. 150--153, especially (1.1.7), (1.1.8), (1.1.10)(ii) and (1.1.13).
The latter sends geometric Frobenius to +1 and gives degree e for a degree-e closed point.
The theorem docstring carries all nine steps of the node's proof with their dependencies.

Searches made before writing:

- `msearch.py` LeanFinder: “The Weil group of a scheme over a finite field is the group of
  natural isomorphisms from a geometric fibre functor to its Frobenius translates, with the
  twisted path multiplication”. Eight results concern general Galois-category automorphism
  groups and finite-field Frobenius; none states the twisted-path group or local formula.
- `msearch.py` Loogle: `"weilGroup"`: zero hits.
- `msearch.py` grep: `twistedPath|[Ww]eil[Gg]roup`: zero Mathlib hits.
- `msearch.py` LeanSearch: “The Weil group is the group of Frobenius twisted etale paths and
  residue field Frobenius is the closed point return path”. Results were finite-field and
  absolute Galois groups and Witt-vector Frobenius; no exact match.
- `rg` in upstream WeilConjectures and side `lean/Sheaf` for twisted-path and Weil-group
  names: the existing Weil group and finite-étale transport were found and read, neither
  gives the group of twisted paths and its closed-point formula. Searching the item id in
  upstream found no declaration. The proposed names were also checked against
  `dag/lean_names_upstream.json`, side Lean and upstream Lean, with no collision.

Edge cases checked before writing: n = 0 identifies Aut(F_b); negative n uses integer powers
of an automorphism; X₀ = Spec k₀ gives one path in each integer degree and hence Z; degree-one
closed points give γ, not its inverse; changing τ conjugates the arithmetic element in the
specified order; the empty scheme is excluded by geometric connectedness and the chosen
geometric point. The empty finite étale cover is included in every cover quantifier (its
pointwise condition is empty, as it should be). No positivity assumption is imposed on a
Weil degree. The fixed closure D.k is arbitrary and the basepoint field need not be D.k.

There is no `STATEMENT-DISPUTED` claim and no statement correction.

The closed-point predicate installs the existing proof `IsAlgClosure.isAlgClosed D.k₀`
inside its definition to infer `IsSepClosed D.k`. This adds no hypothesis and changes no
file-level instance. All universe and term parameters are explicit, and theorem signatures
contain no `let`, local notation, or hidden auto-implicit parameters.

Validation: `scompile.py Q21 lem-real-weil-twisted-paths` compiled the final module cleanly,
both as a sandbox and under its actual library module name. There were no errors or warnings.
All Lean lines are at most 100 characters, exactly one `sorry` occurs, and comparison with
the repository node confirms that `lean` is the only changed field.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
