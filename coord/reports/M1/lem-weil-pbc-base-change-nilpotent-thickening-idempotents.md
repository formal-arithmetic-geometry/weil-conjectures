## Worker report

The module `Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents` states
`AlgebraicGeometry.nilpotent_baseChange_idempotents`, with `sorry`, and introduces no definitions.
There are no node corrections, missing notions, or unusable dependencies.

Hypothesis and clause correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`, including the zero ring.
- An ideal J: `(J : Ideal A)`; a natural exponent at least one: `(N : ℕ) (hN : 1 ≤ N)`.
- J^N = 0: `(hJ : J ^ N = ⊥)`; bottom is the zero ideal.
- A scheme Y and morphism to Spec A: `(Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of A))`.
- The quotient map is `q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))`.
- The specified fibre product is `Y₀ := pullback g q`, and its first projection is
  `i : Y₀ ⟶ Y := pullback.fst g q`. These are local let bindings, not separate definitions.
- Clause (1), closed immersion: `IsClosedImmersion i`.
- Its quasi-coherent kernel ideal sheaf is exactly `i.ker : Y.IdealSheafData`, the recorded
  dependency declaration. For a closed immersion it computes the kernel of the structure
  sheaf map, as `Scheme.Hom.ker_apply` describes on affine opens; closed immersions are
  quasi-compact. No extra quasi-coherence hypothesis is imposed.
- Its Nth power vanishes: `i.ker ^ N = ⊥`, using ideal sheaf powers and zero as bottom.
- Finite order thickening: `IsFiniteOrderThickening i`, imported from the dependency module.
- Homeomorphism of underlying spaces: `IsHomeomorph i`, using the scheme morphism's
  coercion to its point map. This includes continuity, openness, and bijectivity.
- Clause (2): for every `e₀ : Γ(Y₀, ⊤)` with `IsIdempotentElem e₀`, there is exactly one
  `e : {e : Γ(Y, ⊤) // IsIdempotentElem e}` whose image
  `(Scheme.Γ.map i.op).hom e.val` is `e₀`. The unique existential is over idempotents,
  so uniqueness is only among idempotent lifts, exactly as stated. The ring homomorphism
  preserves idempotents automatically; the node's final unique-lifting formulation is
  equivalent to its bijection formulation. Surjectivity of the full global section map
  is not assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`, and `Scheme.Γ` (global sections and their map).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback`
  and `pullback.fst`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies existence for schemes.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `AlgebraicGeometry.Scheme.Hom.ker`,
  `Hom.ker_apply`, and `Scheme.IdealSheafData`'s power and bottom/zero structures.
- `Sheaf.AlgebraicGeometry.Thickening`: `AlgebraicGeometry.IsFiniteOrderThickening`
  (defined as existence of `IsNthOrderThickening`; its full definition was read).
- `Mathlib.Algebra.Group.Idempotent` (via `Mathlib.Algebra.Ring.Idempotent`):
  `IsIdempotentElem`, meaning `e * e = e`.

Edge cases checked: N=1 forces J=0; N=0 is deliberately excluded as in the node.
The zero ring, J=0, the empty scheme, nonaffine schemes, and non-quasi-compact schemes
are not excluded. No nontriviality, Noetherian, properness, separatedness, connectedness,
or surjectivity-on-global-sections hypothesis is added. The universe u is arbitrary;
as with Mathlib's scheme category and Spec, the objects are placed in a common universe.
The underlying-space homeomorphism gives the global-idempotent conclusion even when
restriction on all global sections is not surjective.

Sources checked online because this machine has no local Stacks source checkout:
[09ZU](https://stacks.math.columbia.edu/tag/09ZU) gives preservation of finite order
thickenings by base change; [04EX](https://stacks.math.columbia.edu/tag/04EX) defines them.
The equal-underlying-spaces passage in the proof of
[0G7X](https://stacks.math.columbia.edu/tag/0G7X) constructs idempotents on infinitesimal
neighbourhoods from their clopen decompositions. The module docstring records the four
steps of the DAG proof and each proof lemma it uses.

Searches (via `/home/ubuntu/weil-launcher/msearch.py`, group M1 and this item):

- LeanFinder: `base change nilpotent thickening schemes global section idempotents bijective`:
  eight hits on formally unramified morphisms, open immersions from idempotents, separated
  Spec maps, ideal-sheaf gluing, and ring-level etale idempotents; no exact statement.
- Loogle: `AlgebraicGeometry.IsClosedImmersion, IsHomeomorph`: zero hits.
- Mathlib grep: `thickening|idempotent|IsHomeomorph` in `AlgebraicGeometry`: sixteen hits,
  including formally unramified infinitesimal thickenings and topological maps;
  no nilpotent base-change/global-idempotent theorem.
- LeanSearch: `nilpotent thickening schemes induces bijection on idempotent global sections`:
  service unavailable, Internal Server Error; other searches completed.
- `rg -n 'thickening|[Ii]dempotent|nilpotent.*base.change'` in the upstream
  `WeilConjectures` and project `lean/Sheaf`: upstream has connectedness criteria,
  ring-level etale splitting, and unrelated Artin-Schreier projectors; project has
  thickening definitions and other applications, but no exact theorem.
- Item-id search in `WeilConjectures` and `dag/lean_names_upstream.json`: no hits.
- Exact new declaration/module name search in Mathlib, `WeilConjectures`,
  `dag/lean_names_upstream.json`, and project `lean/Sheaf`: no collisions.

Validation: `scompile.py M1 lem-weil-pbc-base-change-nilpotent-thickening-idempotents`
compiled the module on the server in 1.8 seconds with exit code 0 and no warnings.

## Second reading by M1

I independently opened the item's JSON and Lean module, all seven statement-dependency
nodes, the imported Thickening module, and the Mathlib declarations listed below.
There is no `statement_change`, new definition node, or dependency module in this delivery.
The statement matches the node; no Lean or node repair was needed.

Source reading: because the literature checkout is absent here, I read the actual Stacks
TeX from `https://raw.githubusercontent.com/stacks/stacks-project/master/`:
`more-morphisms.tex`, labels `definition-thickening` and `lemma-base-change-thickening`,
and `perfect.tex`, label `lemma-proper-idempotent-on-fibre`, including its proof.
I also checked [09ZU](https://stacks.math.columbia.edu/tag/09ZU),
[04EX](https://stacks.math.columbia.edu/tag/04EX),
[0G7X](https://stacks.math.columbia.edu/tag/0G7X), and
[00EE](https://stacks.math.columbia.edu/tag/00EE).
The thickening section assumes no properness, Noetherian hypothesis, or field.
The full 0G7X lemma assumes properness, and its formal-functions argument temporarily
assumes a Noetherian base; the node cites only the equal-space/clopen-decomposition step.
That step works for every scheme: glue the sections 1 and 0 on complementary clopens.
It does not use either of those extra assumptions. Empty pieces give the trivial
idempotents, so the nontrivial example in that proof does not restrict this statement.

Independent object/hypothesis/conclusion checklist (all verdicts: exact):

1. Commutative ring A: `(A : Type u) [CommRing A]`; no nontriviality or field instance.
2. Ideal J of A: `(J : Ideal A)`; no finiteness or radical condition.
3. Positive integer exponent and vanishing: `(N : ℕ) (hN : 1 ≤ N)
   (hJ : J ^ N = ⊥)`. Ideal bottom is the zero ideal. Universally binding an arbitrary
   witnessed exponent states the node for each such N, retaining that same N in (1).
4. Scheme Y and the given morphism g: `(Y : Scheme.{u})
   (g : Y ⟶ Spec (CommRingCat.of A))`. The node names g explicitly, so this is the
   permitted explicit structure-map convention. No property of g is assumed.
5. Spec(A/J) to Spec A: `q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))`.
   `Spec.map` is contravariant, so this has the required direction.
6. Fibre product Y₀ and its first projection: `Y₀ := pullback g q` and
   `i : Y₀ ⟶ Y := pullback.fst g q`. Mathlib provides pullbacks of all schemes;
   no existence instance is demanded from the caller.
7. Closed immersion: `IsClosedImmersion i`. Its signature requires a closed embedding
   on points and surjectivity on stalks, the node's sheaf-surjectivity condition.
8. Quasi-coherent kernel ideal sheaf and its Nth power: `i.ker ^ N = ⊥`.
   `Scheme.Hom.ker` is defined for arbitrary morphisms as the largest quasi-coherent
   ideal in the sectionwise kernel; crucially `Hom.ker_apply` identifies it with the
   actual kernel on affine opens for quasi-compact morphisms. A closed immersion is
   affine and quasi-compact, so the preceding conjunct makes this precisely the
   node's kernel, without an extra hypothesis. The ideal-power instance and
   `IdealSheafData.ideal_pow` compute powers on affine opens; zero is defined as bottom.
9. Finite order thickening of Y₀ by Y: `IsFiniteOrderThickening i`. The dependency
   module defines this as `∃ n : ℕ, IsNthOrderThickening n i`, and the latter is
   `IsClosedImmersion i ∧ i.ker ^ (n + 1) = ⊥`. This is exactly 04EX(3), with
   witness N-1; it uses the same kernel and does not impose an additional instance.
10. Homeomorphism of underlying spaces: `IsHomeomorph i`, coercing i to its point map.
    I read its fields: continuity, openness, and bijectivity; this is a homeomorphism,
    rather than only a continuous bijection.
11. Map on global sections: `(Scheme.Γ.map i.op).hom`. `Scheme.Γ_map_op` identifies
    it with `i.appTop`, hence exactly i-sharp from Γ(Y,O) to Γ(Y₀,O).
12. Every idempotent on Y₀: `∀ e₀ : Γ(Y₀, ⊤), IsIdempotentElem e₀ → ...`.
    `IsIdempotentElem` is defined as `e₀ * e₀ = e₀`.
13. Exactly one idempotent lift: `∃! e : {e : Γ(Y, ⊤) // IsIdempotentElem e},
    (Scheme.Γ.map i.op).hom e.val = e₀`. The subtype makes uniqueness range only
    over idempotents; proof irrelevance introduces no additional choice of lift.
    A ring hom preserves idempotents, so this is equivalent to the requested
    bijection on the idempotent sets, including its injectivity clause.

The dependency signatures were read in Mathlib's `Scheme.lean`,
`CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`, `AlgebraicGeometry/Pullbacks.lean`,
`Morphisms/ClosedImmersion.lean`, and `IdealSheaf/Basic.lean`, and in the project's
`Sheaf/AlgebraicGeometry/Thickening.lean`. They render the dependency nodes' notions;
there is no private replacement. All three imports serve the statement.

Edge cases: J=0 allows every positive exponent; N=1 forces J=0 and includes the
zeroth-order thickening. N=0 is excluded by the node itself. The zero ring and empty
scheme are allowed; empty global sections form the zero ring and have one idempotent.
Nonaffine, non-quasi-compact, disconnected schemes and all characteristics are included.
There is no finite index set or nonempty assumption. The universe u is arbitrary:
A and Y live in the same Mathlib scheme category, and any different size bounds can be
placed in a common larger universe. Inspection found no unbound variable or universe.

Independent searches, using different wording from the first reader:

- LeanFinder via msearch: `restriction of global sections along a closed immersion
  with nilpotent defining ideal gives equivalence of idempotents`: eight hits, including
  `IsClosedImmersion.overEquivIdealSheafData`, subscheme section descriptions, and module
  restriction adjunctions; none states this theorem.
- Loogle via msearch: `"idempotent", "Scheme"`: no hits.
- LeanSearch via msearch: `global sections idempotents nilpotent closed immersion scheme
  bijection`: unavailable, Internal Server Error; recorded as unavailable, not a no-match.
- Independent rg of Mathlib AlgebraicGeometry, all upstream WeilConjectures, and project
  lean/Sheaf for nilpotent, idempotent, thickening, idempotent lifting/restriction, and
  nilpotent base change: ring/local criteria, dual-number constructions, connectedness,
  and other applications only. I opened upstream
  `Scheme.bijective_appTop_idempotent_of_henselianRing` in `HenselianFiniteEtale.lean`:
  it requires a proper morphism and a HenselianRing instance, so it does not state this
  arbitrary-scheme nilpotent-thickening theorem and does not include clause (1).
- Exact declaration/module-name rg across Mathlib, upstream, project lean/Sheaf and
  dag/lean_names_upstream.json: no collisions.

Mismatch/change inventory: none in the Lean signature, node, imports, definitions, or
proof docstring. The four docstring steps reproduce the node's ideal computation,
vanishing of its power, prime-ideal/surjectivity argument, and natural clopen/idempotent
bijection. The only proof is `sorry`; no data definition or proof was introduced.
Second reading changed only this report and appended independent search records.
The node's `lean.statement` was compared byte-for-byte with the file signature and matches;
all source lines are at most 100 characters.

Second-reader compilation with scompile.py completed on the server in 1.7 seconds,
exit code 0, with no errors or warnings.
