## Worker report

`Sheaf.CategoryTheory.Galois.StacksGaloisAxioms` defines the Galois-object
predicate and states the seven consequences of the Stacks Galois category
axioms as one theorem. Its only proof is `sorry`.
The source is Stacks, Fundamental Groups of Schemes, Lemma 0BN0 and the
following paragraph on Galois objects (`pione.tex`, lines 407-485 in the local
review checkout). The project repository's `literature/stacks-project/pione.tex`
and the node's blueprint Markdown were absent on this machine; the node and
the locally available Stacks source agree on the mathematical clauses.

The common hypothesis is `{C : Type u} [Category.{v} C] (F : C ⥤ Type w)`
and `(hG : IsStacksGaloisCategory F)`. The latter is precisely the four-part
Stacks axiom structure from `Sheaf.CategoryTheory.Galois.StacksGaloisCategory`:
finite limits and colimits, decomposition into finite coproducts of connected
objects, finite fibres, and exactness plus reflection of isomorphisms.

1. `Functor.Faithful F` renders faithfulness.
2. For every `f : X ⟶ Y`, `Mono f ↔ Function.Injective (F.map f)` and
   `Epi f ↔ Function.Surjective (F.map f)` render both directions of both
   characterizations.
3. For every `X`, `Nonempty (IsInitial X) ↔ IsEmpty (F.obj X)` renders
   initial iff empty; `Nonempty (IsTerminal X) ↔ ∃ s : F.obj X,
   ∀ t : F.obj X, t = s` renders terminal iff singleton, including
   nonemptiness of the singleton.
4. `IsConnected X → IsConnected Y → ∀ f : X ⟶ Y, Epi f` renders every
   morphism between connected objects being epi.
5. For connected `X`, `∀ (a b : X ⟶ Y) (s : F.obj X),
   F.map a s = F.map b s → a = b` renders agreement at one element.
6. `IsStacksGaloisObject F X` is defined in full as `IsConnected X ∧
   Nat.card (Aut X) = Nat.card (F.obj X)`. For connected `X` and
   `s : F.obj X`, the theorem gives injectivity of
   `fun g : Aut X => F.map g.hom s`, the `Nat.card` bound, and both
   `IsStacksGaloisObject F X ↔ Nat.card (Aut X) = Nat.card (F.obj X)` and
   `IsStacksGaloisObject F X ↔ ∀ t : F.obj X, ∃ g : Aut X,
   F.map g.hom s = t`. The latter is transitivity at the given `s`.
7. `I : Type wI` and `J : Type wJ` with `[Finite I] [Finite J]` are arbitrary
   finite index sets. `Nonempty (IsColimit (Cofan.mk X ιX))` and its `Y`
   counterpart assert the two chosen coproduct presentations;
   `(∀ i, IsConnected (Xi i))` and `(∀ j, IsConnected (Yj j))` assert each
   connectedness hypothesis. For every `f : X ⟶ Y`, the conclusion gives
   `α : I → J` and `component : ∀ i, Xi i ⟶ Yj (α i)` with
   `∀ i, ιX i ≫ f = component i ≫ ιY (α i)`, exactly the component equation.

Dependency declarations used: `CategoryTheory.IsStacksGaloisCategory` from
`Sheaf.CategoryTheory.Galois.StacksGaloisCategory`; `CategoryTheory.Limits.IsInitial`
and `CategoryTheory.Mono` (Mathlib); `CategoryTheory.Epi` and
`CategoryTheory.Limits.IsTerminal` (Mathlib);
`CategoryTheory.PreGaloisCategory.IsConnected` (Mathlib Galois.Basic);
`CategoryTheory.Limits.Cofan.mk` and `CategoryTheory.Limits.IsColimit`
(Mathlib Limits.Shapes.Products). Their signatures and docstrings were read.

Edge cases: finite `I` and `J` include empty types. With empty `I`, the
component conclusion is vacuous, as any map from the initial coproduct is
determined by the empty family. With nonempty `I` and empty `J`, the theorem
would imply there is no morphism under the connectedness hypotheses, as
expected. Empty fibres fail the singleton predicate because it includes an
element. The automorphism clause is conditional on `s : F.obj X`, as in the
node. Independent universes `wI` and `wJ` avoid restricting the finite
index types to the fibre's universe; no characteristic assumption is added.

Searches: `msearch.py leanfinder` with “consequences of Galois category
axioms faithful fiber functor mono iff injective epi iff surjective connected
objects automorphism cardinal finite coproduct morphisms” found Mathlib's
`GaloisCategory`, `PreGaloisCategory`, and `IsGalois`, but no declaration for
the Stacks axiom pair and all seven clauses. `msearch.py loogle` with
`PreGaloisCategory.FiberFunctor, IsStacksGaloisCategory,
initial_iff_fiber_empty` returned zero hits (the first unqualified name was
not resolved). `msearch.py grep` with `galois|Galois|fiber` in
`CategoryTheory/Galois` found per-clause Mathlib results, but no exact match.
`rg` in the source `WeilConjectures`, Mathlib, and repository `lean/Sheaf`
found no `stacksGaloisCategory_axioms` or `lem-galois-axioms` declaration.
Mathlib's `PreGaloisCategory` has different axioms and a functor to
`FintypeCat`, so its per-clause results do not state this theorem.

Server `scompile.py G1 lem-galois-axioms` compiled the module cleanly.

## Second reading by G1

I reread `dag/nodes/sec-curve-estimates/lem-galois-axioms.json` against
`StacksGaloisAxioms.lean` and the dependency declarations.

1. The common object is a category `C : Type u` with
   `[Category.{v} C]`, a functor `F : C ⥤ Type w`, and
   `hG : IsStacksGaloisCategory F`; this is exactly the node's
   Galois-category setting, with no extra assumptions.
2. Faithfulness is `Functor.Faithful F`. For every `f : X ⟶ Y`, the two
   equivalences `Mono f ↔ Function.Injective (F.map f)` and
   `Epi f ↔ Function.Surjective (F.map f)` render both directions of the
   node's mono and epi clause, using the Mathlib `Mono` and `Epi` notions.
3. For every `X`, `Nonempty (IsInitial X) ↔ IsEmpty (F.obj X)` and
   `Nonempty (IsTerminal X) ↔ ∃ s, ∀ t, t = s` render initial iff empty
   and final iff singleton, including the required singleton inhabitant.
4. `IsConnected X → IsConnected Y → ∀ f : X ⟶ Y, Epi f` is exactly the
   connected-morphism clause; `IsConnected` is the dependency's
   `PreGaloisCategory.IsConnected`.
5. For connected `X`, the quantified `a b` and `s : F.obj X` with
   `F.map a s = F.map b s → a = b` exactly state agreement on one fibre
   element.
6. `IsStacksGaloisObject F X` is defined as
   `IsConnected X ∧ Nat.card (Aut X) = Nat.card (F.obj X)`, matching the
   node's Galois-object convention. Under connected `X` and `s`, the
   theorem gives injectivity of evaluation on `Aut X`, the cardinal bound,
   equality characterization, and the equivalent transitivity statement.
7. The final quantifier uses arbitrary `I : Type wI`, `J : Type wJ` with
   `[Finite I] [Finite J]`, families `Xi`, `Yj`, objects `X`, `Y`, chosen
   coprojections, and `Nonempty (IsColimit (Cofan.mk ...))`. Connectedness
   of every summand and the resulting `α : I → J`, component morphisms, and
   equation `ιX i ≫ f = component i ≫ ιY (α i)` match the node clause.

Edge cases checked: finite index types may be empty, so empty coproducts and
the vacuous component conclusion are included; an empty target index with a
nonempty source makes the existential impossible as expected. The terminal
clause excludes an empty fibre by requiring an element. The automorphism
claims are conditional on `s : F.obj X`, and the independent universes
`wI`, `wJ`, `w`, `v`, `u` impose no restriction on the node's cases. No
characteristic, nonemptiness, Noetherian, or finiteness assumptions beyond
those in `IsStacksGaloisCategory` were added.

Searches were repeated with `msearch.py` (`grep` for
`IsStacksGaloisObject|stacksGaloisCategory_axioms`, no hits; `leanfinder` for
Galois-category axioms, hits only Mathlib's `PreGaloisCategory` declarations)
and `rg` in the source repository and Mathlib. No exact existing declaration
was found. The Mathlib candidates use the SGA1/Lenstra `PreGaloisCategory`
axioms and therefore do not state this Stacks result.

No mismatch was found. The module and node statement were left unchanged.
