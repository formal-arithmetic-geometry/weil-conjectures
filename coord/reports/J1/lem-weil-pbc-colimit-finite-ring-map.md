## Worker report

The module `Sheaf.RingTheory.FiniteMapColimitDescent` states
`RingHom.exists_finite_tensorProductMap_of_colimit` with proof `sorry`.
It renders precisely Stacks Project, Algebra, Lemma 10.168.3, Tag 07RG:
https://stacks.math.columbia.edu/tag/07RG . The local literature checkout lacks
`algebra.tex`, so the full statement and proof were read on the Stacks website.
No node correction, new notion, or dependency module was necessary.

Hypothesis and conclusion correspondence:

- A directed set is `{I : Type w} [PartialOrder I] [IsDirected I (· ≤ ·)]`.
  The distinguished element `(i₀ : I)` supplies nonemptiness; the symbol 0 in
  the node denotes this element and does not require a least element or a zero structure.
- The directed system of commutative rings with compatible transition maps is
  `(F : I ⥤ CommRingCat.{u})`: functoriality supplies identity and composition laws.
- Its colimit A is `(colimit F : CommRingCat.{u})`, with `[HasColimit F]`.
  This is exactly the categorical colimit recorded by
  `def-weil-pbc-category-colimit`; no direct-limit surrogate is introduced.
  The existence binder just expresses the colimit given in the node, and permits
  arbitrary index universe `w` independently of ring universe `u`.
- The distinguished ring A₀ is `F.obj i₀`. The two commutative algebras are
  `(B₀ : Type v) (C₀ : Type t) [CommRing B₀] [CommRing C₀]`, together with
  `[Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]`.
- The A₀-algebra homomorphism is `(φ₀ : B₀ →ₐ[F.obj i₀] C₀)`.
- The finite-type hypothesis is `(hft : φ₀.FiniteType)`: `AlgHom.FiniteType`
  means finite generation of the target as an algebra over the source through φ₀.
- The A₀-algebra structure on A is installed by the first `letI`, using exactly
  `(CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra`.
- The colimit map φ = id_A ⊗ φ₀ is
  `Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀`.
  Its domain and target are A ⊗[A₀] B₀ and A ⊗[A₀] C₀, respectively.
- The assumption that φ is finite is the premise `.Finite →`.
  `AlgHom.Finite` uses `RingHom.Finite`, hence module finiteness for the
  scalar action supplied by precisely this map, not by an unrelated instance.
- The conclusion `∃ (i : I) (h : i₀ ≤ i), ...` supplies a stage above i₀.
  The second `letI` uses `(F.map (homOfLE h)).hom.toAlgebra`, exactly the transition
  map A₀ → Aᵢ. Finally
  `(Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).Finite`
  is the required finiteness of id_Aᵢ ⊗ φ₀ between Bᵢ and Cᵢ.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`
  and `CategoryTheory.Limits.colimit.ι` (the dual-generated signatures and
  docstrings in HasLimits.lean were read). Imported through
  `Mathlib.Algebra.Category.Ring.Colimits`. These implement the sole statement
  dependency `def-weil-pbc-category-colimit`, a Mathlib leaf.
- `Mathlib.RingTheory.FiniteType`, `AlgHom.FiniteType` and `RingHom.FiniteType`.
- `Mathlib.RingTheory.Finiteness.Defs`, `AlgHom.Finite` and `RingHom.Finite`,
  available through the finite-type import.
- `Mathlib.RingTheory.TensorProduct.Maps`, `Algebra.TensorProduct.map` and
  its pure-tensor formula `map_tmul`; `RingHom.toAlgebra` supplies scalar actions.

Edge cases checked before writing: an empty index set cannot have the specified
i₀; a singleton diagram is allowed; i₀ need not be least; zero rings and zero
algebras are permitted throughout; no transition map or φ₀ need be injective.
An empty set of algebra generators is permitted by `FiniteType`. All four
universes are explicitly bound, and no finite presentation or Noetherian
assumption has been added. The source confirms exactly the two finiteness
hypotheses in the node. No statement dispute was found.

Searches for existing statements (2026-10-11):

- `msearch.py ... leanfinder "A finite type algebra map becomes finite after
  tensoring with a directed colimit of rings, then it is finite after tensoring
  with some stage"`: eight hits including `RingHom.Finite.tensorProductMap`,
  `Algebra.FiniteType.baseChange`, `Algebra.FinitePresentation.baseChange` and
  `TensorProduct.Algebra.exists_of_fg`. These are stability or finite-support
  results, not the asserted descent theorem.
- `msearch.py ... loogle "RingHom.Finite, CategoryTheory.Limits.IsColimit"`:
  zero hits.
- `msearch.py ... grep "07RG|finite_of_isColimit|Finite.*DirectLimit" RingTheory`:
  zero hits.
- `rg` of the full upstream `WeilConjectures` and project `lean/Sheaf` trees for
  colimit/finite patterns and Tag 07RG: only unrelated category finiteness,
  finite presentation and colimit constructions; no matching statement.
  Searching the exact node id in upstream also found nothing.
- Read Mathlib's tensor-product map, finite-type and finite-map definitions;
  verified that their signatures give the exact maps and finiteness predicates.
  Searched `dag/lean_names_upstream.json` for the selected declaration name:
  no collision.

Validation: server `scompile.py J1 lem-weil-pbc-colimit-finite-ring-map` compiled
this module in 1.4 seconds with exit code 0 and no warnings. The five-step
natural-language proof from the node is carried in the theorem docstring,
including the three proof dependencies. No proof was filled.

Additional required search: `msearch.py ... leansearch "A finite type algebra map
becomes finite after base change to a directed colimit of rings if and only if
it becomes finite at some stage"` returned `UNAVAILABLE 0 hit(s) | service
unavailable: Internal Server Error`. No verdict is inferred from that service
failure; LeanFinder, Loogle and source searches above were available.

Delivery dry run: printed OK; server compilation and preflight passed except
for the independent second reading, which is reserved for the second reader.
Nothing was pushed.


## Second reading by J1

I independently opened the item's node and module, the sole statement dependency
`def-weil-pbc-category-colimit` and its recorded Mathlib declaration, and the
Mathlib definitions of both finiteness predicates and the tensor-product map.
The local Stacks checkout is absent. I read Tag 07RG on the Stacks website and
fetched the upstream `algebra.tex` into this item's scratchpad, reading
`lemma-colimit-finite`, its proof, the section introduction and chapter
Conventions. The latter requires commutative unital rings and explicitly permits
the zero ring; the section adds no standing Noetherian or field hypothesis.
Source: https://stacks.math.columbia.edu/tag/07RG and
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex .

Here is my object/hypothesis/conclusion inventory, matched to the Lean:

1. Directed set I: `{I : Type w} [PartialOrder I]
   [IsDirected I (· ≤ ·)]`. Correct: a directed poset, with no least-element,
   countability or finite-index hypothesis.
2. Compatible commutative ring system A_i: `F : I ⥤ CommRingCat.{u}`.
   Correct: the poset category's arrows encode inequalities and the functor laws
   encode the transition-map identities and compositions.
3. Colimit A with its coprojections: `[HasColimit F]`, `colimit F` and
   `colimit.ι F i₀`. Correct: these are exactly the chosen categorical colimit
   of the dependency node, not a replacement notion. I read the generated dual
   signatures/docstrings of `limit` and `limit.π` in HasLimits.lean: the former
   produces `colimit (F : J ⥤ C) [HasColimit F] : C`, the latter the coprojection.
   The existence instance records the given colimit, rather than an additional
   mathematical finiteness assumption. Choosing this colimit loses no case:
   any specified colimit is uniquely isomorphic compatibly with coprojections,
   and the resulting base-change maps have the same module-finiteness property.
4. Distinguished element 0 of I: `(i₀ : I)`. Correct: 0 is just an index in the
   source, not a least element, numeric zero or `OrderBot`.
5. Commutative A₀-algebras B₀ and C₀: `(B₀ : Type v) (C₀ : Type t)`, their
   `CommRing` instances, and both `Algebra (F.obj i₀)` instances. Correct, with
   neither finite type over A₀ nor nontriviality imposed.
6. A₀-algebra map φ₀: `(φ₀ : B₀ →ₐ[F.obj i₀] C₀)`. Correct: compatibility
   with the given A₀-structures is part of AlgHom.
7. C₀ finite type over B₀ via φ₀: `(hft : φ₀.FiniteType)`. Correct: I read
   `AlgHom.FiniteType`, which delegates to `RingHom.FiniteType` and installs
   the algebra structure from φ₀, not an arbitrary B₀-action on C₀.
8. A as A₀-algebra via the coprojection: the first `letI` uses
   `(CommRingCat.Hom.hom (colimit.ι F i₀)).toAlgebra`. Correct map and action.
9. B = A ⊗[A₀] B₀, C = A ⊗[A₀] C₀ and φ = id_A ⊗ φ₀: the domain,
   codomain and value of `Algebra.TensorProduct.map
   (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀`. Correct: I read
   `map` and `map_tmul`; it sends a ⊗ b to a ⊗ φ₀(b).
10. φ finite: `.Finite →`. Correct: `AlgHom.Finite` delegates to
    `RingHom.Finite`, which installs this map's algebra structure and asks for
    `Module.Finite` of the codomain over the domain. Thus this is precisely C
    finitely generated as B-module via φ, not finite cardinality or finite type.
11. There is a stage i above 0: `∃ (i : I) (h : i₀ ≤ i)`. Correct existential
    order, with no uniform stage chosen before the input algebras or map.
12. Aᵢ as A₀-algebra via the transition map: the second `letI` uses
    `(CommRingCat.Hom.hom (F.map (homOfLE h))).toAlgebra`. Correct; h is used
    in the map rather than an unrelated A₀-algebra instance.
13. Bᵢ, Cᵢ, φᵢ and finiteness at this stage:
    `(Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).Finite`.
    Correct domain Aᵢ ⊗[A₀] B₀, codomain Aᵢ ⊗[A₀] C₀, pure-tensor action,
    and module-finiteness conclusion. No conclusion clause is omitted.

Edge cases: an empty I is already excluded by the source's specified 0 ∈ I,
which Lean renders by i₀; a singleton system and an arbitrary nonleast i₀ are
allowed. Zero rings, zero algebras and zero tensor products are allowed, as are
noninjective transition maps and φ₀. No characteristic constraint occurs. A
finite generating family may be empty (the analogue of n = 0); the FiniteType
predicate imposes no positive generator count. Schemes and empty schemes do not
occur in this node. Universes w, u, v, t are explicitly declared and independent;
there is no forced equality between the index and ring universes. For a diagram
whose colimit needs a larger carrier universe, take u large enough to contain
that colimit and the stages. No case of the source is lost.

Independent searches, using different wording from the first reader:

- LeanFinder through `msearch.py`: "module finiteness of an algebra homomorphism
  descends from a filtered direct limit to one of its base changes". Eight hits,
  including finite/finite-type base-change stability, essentially finite type
  composition and quasi-finite base change; none states this descent direction.
- Loogle through `msearch.py`: `"Finite", "colimit"`. Twelve hits about finite
  categorical colimits and preservation/reflection, not finite algebra maps.
- LeanSearch through `msearch.py`: "finite type ring homomorphism whose scalar
  extension to a filtered colimit is module finite is module finite at a finite
  stage". Service unavailable (Internal Server Error); no absence verdict is
  inferred from this failed service.
- `rg` on Mathlib RingTheory and Algebra/Category/Ring, and on the full upstream
  WeilConjectures and project lean/Sheaf trees, for Tag 07RG, the proposed name
  and finite/colimit/DirectLimit combinations. No exact theorem or name collision.
  I read Mathlib Algebra/Category/Ring/FinitePresentation.lean: its two nearby
  theorems concern eventual equality and factorization of maps from finitely
  presented algebras, not descent of finiteness of this base-changed map.
  The project's FinitePresentationColimit theorem concerns finitely presented
  modules and their morphisms, not this finite-type algebra-map assertion.
  The name also has no entry in dag/lean_names_upstream.json.

H4/H5/H6/H8/H9: all notions use Mathlib, the sole dependency's recorded notion
is used, and no additional definition node or dependency module is needed.
There are no definitions with postponed data. The only theorem proof is `sorry`.
The module and declaration docstrings identify the source and blueprint node;
the five proof steps cover generators at every stage, finite implies integral,
coefficient lifting, eventual vanishing of relations, and finite integral
 generators imply module finiteness, citing the node's three proof dependencies.
All imports supply notions used in the signature; the header, topic, namespace
and line widths conform. No variable or universe is unbound. The node's
`lean.statement` is verbatim equal to the theorem signature (checked directly).
There is no `statement_change`, so corrected-statement/citer review is inapplicable.

Verdict: no mismatch found. I left the Lean module and node unchanged and added
this independent review only. Fresh server compilation through scompile.py
returned exit code 0, compiled in 1.4 seconds, with no warnings.
