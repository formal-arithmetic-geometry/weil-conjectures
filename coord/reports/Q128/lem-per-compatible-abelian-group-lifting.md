## Worker report

The module `Sheaf.GroupTheory.CompatibleAbelianGroupLifting` states
`AddCommGroup.exists_compatible_lift_of_bijective_nsmul`, with one `sorry` and no
new definitions. Only the item's `lean` record is changed. There are no new nodes,
dependency repairs, or statement corrections.

The statement is matched hypothesis by hypothesis and clause by clause:

| Node text | Lean rendering |
| --- | --- |
| Abelian groups A, B, E, E₀, J | Five type binders, each with its own explicitly declared universe, and five `AddCommGroup` instances |
| A and B finitely generated as integer modules for their canonical integer action | `[Module.Finite ℤ A] [Module.Finite ℤ B]`; the canonical integer module instances are inferred from the additive group structures, with no arbitrary scalar action supplied |
| Homomorphism u : A → B | `(u : A →+ B)` |
| K = ker u, finite | The actual subgroup `u.ker`, with `[Finite u.ker]` |
| C = B/u(A) | The actual quotient `B ⧸ u.range` |
| C_tors = {c : C : there exists n > 0 with nc = 0}, finite | `AddCommGroup.torsion (B ⧸ u.range)` and its `Finite` instance binder |
| Homomorphisms J → E → E₀ | `(i : J →+ E) (π : E →+ E₀)` |
| i injective | `hi : Function.Injective i` |
| π surjective | `hπ : Function.Surjective π` |
| ker π = i(J) | `hexact : π.ker = i.range` |
| Multiplication by the order of K is an automorphism of J | `hK : Function.Bijective (fun j : J ↦ Nat.card u.ker • j)` |
| Multiplication by the order of C_tors is an automorphism of J | `hC : Function.Bijective (fun j : J ↦ Nat.card (AddCommGroup.torsion (B ⧸ u.range)) • j)` |
| Given homomorphisms a : A → E and b₀ : B → E₀ | `(a : A →+ E) (b₀ : B →+ E₀)` |
| πa = b₀u | `hcompat : π.comp a = b₀.comp u` |
| A homomorphism b : B → E exists | `∃ b : B →+ E` |
| bu = a and πb = b₀ | `b.comp u = a ∧ π.comp b = b₀` |

Multiplication by a natural number is additive on an abelian group, so bijectivity
of these functions is exactly the automorphism condition, including additivity of
their inverse. `Nat.card` measures the actual finite subgroup types and needs no
chosen enumeration. The torsion subgroup's membership is `IsOfFinAddOrder`, which
Mathlib's `isOfFinAddOrder_iff_nsmul_eq_zero` identifies with precisely a positive
annihilating integer. There is no need for a new notion or auxiliary hypothesis.

Dependency declarations read and used:

- `def-weil-finitely-generated-module` records `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs`. I read its full class declaration and
  docstring: the top submodule is finitely generated. The adjacent
  `Module.Finite.iff_addGroup_fg` confirms the integer-module interpretation.
  Its recorded module is imported publicly.
- Mathlib's `AddCommGroup.torsion` in `Mathlib.GroupTheory.Torsion` is used directly;
  its source and generated additive interface were checked, together with the
  finite-order characterization in `Mathlib.GroupTheory.OrderOfElement`.
- Kernel, image, quotient, composition and cardinality use Mathlib's
  `AddMonoidHom.ker`, `AddMonoidHom.range`, quotient by an additive subgroup,
  `AddMonoidHom.comp`, and `Nat.card` through these imports.
- The sole proof dependency, `lem-sfb-compatible-abelian-group-lifting`, has a
  byte-for-byte identical natural-language statement but no recorded Lean module
  or declaration in the read repository. It therefore supplies no import yet.
  The theorem docstring carries the node's complete one-step proof: apply that
  lemma to the same groups and maps to obtain both equalities. The theorem is
  left `sorry`, as required for stage 2.

Source check: I read ILO Exposé XVI, printed pp. 252–253 (PDF pp. 258–259),
Proposition 3.6.3 and Lemma 3.6.4. These provide the Kato chart context and the
cyclic correction calculation; they do not claim this general lifting lemma.
The module and report preserve the node's explicit agent-formulated provenance.

Edge cases checked mathematically before finalizing:

- The trivial kernel and trivial torsion subgroup each have cardinality one,
  making the respective multiplication map the identity, as explicitly required.
- All zero groups are permitted. There is no `Nontrivial` assumption and no
  spurious zero-order convention. An additive group always has its zero element.
- With A = 0 and B free of finite rank, C_tors is trivial; the claim is ordinary
  lifting of finitely many free generators through the surjection π.
- With u the identity, the lift must be a, and the compatibility hypothesis gives
  the required equality with b₀. Both finite subgroup orders are one.
- For u : ℤ → ℤ given by multiplication by a positive d, K is trivial and the
  torsion cokernel has order d. The statement retains exactly the required
  bijectivity of multiplication by d on J, rather than assuming divisibility
  by every integer or that J is finite.
- J = 0, E₀ = 0, and a zero map u remain covered when the actual finite-kernel
  and invertibility hypotheses hold. No independent universe equality excludes
  differently sized groups.

Searches performed with `msearch.py Q128 lem-per-compatible-abelian-group-lifting`:

1. LeanFinder: `Lift compatible homomorphisms of finitely generated abelian groups
   through a surjection when the finite kernel and torsion cokernel orders act
   bijectively on its kernel`. Eight hits: `AddMonoidHom.liftOfSurjective`,
   `isZGroup_of_coprime`, two coprime cyclicity results, `ModN.liftEquiv`,
   `AddGroup.fintypeOfDomOfCoker`, `Abelianization.lift`, and the finite-generation
   free-group presentation theorem. None gives this relative compatible lift.
2. Loogle: `"AddMonoidHom", "lift"`. Twelve hits, primarily
   `liftOfRightInverse` and `liftOfSurjective` plus their compatibility lemmas,
   and unrelated free-group/topological lifts. Those factor a map through a
   surjection after kernel containment; they do not extend the specified map
   while lifting a second map using finite-order hypotheses.
3. Mathlib grep, subdirectory `GroupTheory`:
   `(lift|extend).*(AddMonoidHom|AddCommGroup)|(AddMonoidHom|AddCommGroup).*(lift|extend)`.
   Six hits, concerning free abelian group lifts and action homomorphisms;
   no compatible-lifting statement.
4. LeanSearch: `Lift compatible homomorphisms of finitely generated abelian groups
   across an exact sequence when the kernel and torsion cokernel orders act
   invertibly on its kernel`. Eight hits: quotient lifts, short-complex kernel
   lift, free abelian lift composition, abelian mono lift, categorical image lift,
   `ZMod.lift`, and `AddMonoidHom.liftOfSurjective`. These have different domains
   or hypotheses and none asserts the required existence theorem.
5. Project `rg` over `lean/WeilConjectures`, `lean/Sheaf` and
   `dag/lean_names_upstream.json` for compatible abelian lifting and both item ids:
   only unrelated compatibility text and a docstring referencing the sfb DAG
   lemma, not a Lean declaration. The focused group-theory search found only an
   unrelated Tate-module comment. Exact `grep -rn` of this item id in
   `lean/WeilConjectures` returned no matches. A declaration-name search in Mathlib
   and both source trees returned no existing declaration.

The same sfb DAG statement is recognized and reused as the proof plan, not
recreated as a definition. When its declaration is available it can also serve as
an existing attachment for this duplicate node. No usable declaration was present
at the time of this delivery. No statement fault or dispute was found.

Validation: the prescribed `scompile.py` compiled the file both as a sandbox
module and under its intended library module name, with no errors or warnings.

## Second reading by Q128

This is the author's separate second reading; the maintainer provides the
independent review. I reopened the item and the final module and checked every
row of the correspondence above. In particular, `hexact` is equality of the
actual kernel and actual image, not merely vanishing of the composite; the
cokernel is by `u.range`, not by `u.ker`; the torsion subgroup is the actual
Mathlib torsion subgroup; and each `Nat.card` is of its finite subgroup, not
of the ambient group. The two bijectivity hypotheses concern multiplication on
J, not on E or E₀. Both maps a and b₀ are universally given and their compatibility
is an input; b is the single existential output and satisfies both specified
equalities. The five universes and all variables are explicitly bound.

No mismatch was found and no statement change was needed. The source attribution
correctly distinguishes the agent-formulated group lemma from ILO's chart
statements. The only theorem has `sorry` as its proof, and no definitions or local
notations obscure the recorded statement.
