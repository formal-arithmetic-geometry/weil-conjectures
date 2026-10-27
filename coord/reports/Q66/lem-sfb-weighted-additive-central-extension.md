## Worker report

The delivery states `AlgebraicGeometry.weightedAdditiveCentralExtension_splits` and adds
one definition node for its missing group-sheaf extension interface. The theorem proof is
`sorry`; the helper module has only actual constructions and a structure declaration.
The item's natural-language statement, proof and proof dependencies are unchanged.

Hypothesis and clause correspondence:

- The arbitrary base is `S : Scheme.{u}`. The kernel scheme is `Z : Over S` with
  `[GrpObj Z]` and `[IsCommMonObj Z]`. Its relative separatedness is `[IsSeparated Z.hom]`,
  whose defining field is `IsClosedImmersion (pullback.diagonal Z.hom)`.
- `Scheme.fppfTopology.over S` is Mathlib's topology on all schemes over S, induced by
  jointly surjective flat locally finitely presented families. `E.F` is a functor into
  `GrpCat`, and `E.isSheaf` requires unique gluing of its underlying sets. No representability
  of F or sectionwise surjectivity of q is assumed.
- `fppfAdditiveGroup S` is the composite of `Over.forget`, `Scheme.Γ`, the forgetful
  functors to additive commutative groups, `AddCommGrpCat.toCommGrp`, the forgetful
  functor to groups,
  and `GrpCat.uliftFunctor`. Its sections are exactly lifted global sections of the
  structure sheaf with addition written multiplicatively. In particular its `1` is zero.
- `E.i` is a natural homomorphism from `yonedaGrpObj Z` (lifted into a common universe).
  `E.q` is a natural homomorphism to the additive quotient. `injective_i` and `exact_i_q`
  identify Z with its entire kernel on every test scheme. `locallySurjective_q` uses
  Mathlib `Presheaf.IsLocallySurjective`; `central` says every kernel section commutes
  with every middle section. These are exactly the stated central exactness conditions.
- `E.action T` is a monoid homomorphism from the actual units `Γ(T.left, ⊤)ˣ` into
  `MulAut (E.F.obj (op T))`. Thus this is an action by group automorphisms, including
  the identity and product laws. `action_natural` restricts both the unit and the
  section along every morphism of S-schemes. `action_i` fixes the kernel pointwise.
  `action_q` gives the required quotient action using `fppfAdditiveWeight`.
- `k : ℤ` and `hk : k = 2 ∨ k = -2` give precisely the two weights. The weight helper
  uses integer powers in the units group before coercing to the ring, so negative
  weight means inverse square without any field assumption.
- The first conclusion quantifies all test schemes and all pairs of sections and
  asserts `x * y = y * x`. This is commutativity of the existing group laws on F.
- The second conclusion is `∃! j` in the category of group-valued functors. Thus j
  is a natural group homomorphism, not an arbitrary section on sets. `j ≫ E.q = 𝟙 _`
  is the section identity. The pointwise equation with `E.action` is equivariance
  for all local units and additive sections. Uniqueness is among exactly these maps.
- The final conjunct quantifies every natural group homomorphism from the actual
  additive quotient to `yonedaGrpObj Z`, assumes its invariance for all test schemes,
  units, and sections, and concludes its value is `1` on every section. It is the
  trivial homomorphism assertion, not just vanishing on units or on base sections.

Dependency declarations read and used: `AlgebraicGeometry.Scheme` and its hom type
(Mathlib.AlgebraicGeometry.Scheme, def-pc-scheme); `AlgebraicGeometry.IsClosedImmersion`
(Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion, def-weil-closed-immersion), through
`IsSeparated`. The new definition module reuses Mathlib `GrpObj`, `IsCommMonObj`,
`yonedaGrpObj`, `Presheaf.IsSheaf`, `Presheaf.IsLocallySurjective`, and the over topology.
The existing def-sc-group-scheme and def-sc-gm-ga concern a field base; neither gives
this arbitrary-scheme central extension datum. No private copy of their notions is made.
The two proof dependencies lem-sfb-unit-power-fppf-surjective and
lem-sfb-monic-principal-open-fppf have no Lean records at the time of this delivery;
there are consequently no stated proof modules to import. All eight proof steps,
including where those nodes enter, are retained in the theorem docstring.

Source read: Conrad, Reductive group schemes,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed pp.127–128,
the additive commutator paragraph and Lemma 4.3.2 including its proof. The source
works with fppf group sheaves and a separated commutative kernel, not just abstract
group extensions. The given node expands its local lifting and gluing argument.

Edge cases checked: empty S and empty test schemes (no Nonempty assumptions), arbitrary
characteristic including 2 and 3, nonreduced bases, negative weight, trivial kernel,
and a middle sheaf not represented by a scheme. There is no division by a ring integer,
no square-root choice in a definition, and no chosen lift of q. The arbitrary universe v
allows larger section sets for F; Γ and the represented Z functor are canonically
lifted into the same containing universe. The site is still all `Scheme.{u}` over S,
with no forced equality between object and morphism universes.

Searches: msearch leanfinder for the weighted splitting theorem returns abstract
AddGroupExtension and GroupExtension splitting results, not a match. Loogle for
`GrpObj, Scheme.fppfTopology` returns no hits (unknown GrpObj at the service).
msearch LeanSearch for central fppf extensions returns AddGroupExtension and unrelated
cohomology. Further LeanSearch and LeanFinder searches for the extension datum return
abstract group extensions, root data, and group actions, not this definition. msearch
grep `WeightedAdditiveExtension|central.?extension|fppf.*group` in AlgebraicGeometry
returns no hits. Direct rg of Mathlib, WeilConjectures, and Sheaf found the existing
fppf topology, over-site construction, global-sections functor, and group-object
Yoneda functor; those are reused. Direct searches for the item id and equivariant
central-extension splitting in both project source trees found no matching theorem.
DAG definition searches for central exact sequences, torus actions and group sheaves
found only unrelated field-base or equivariant-module notions. Blueprint search for
`weighted additive` found no blueprint node. The helper's node stores the real search
records, including their query, hits and digest. No statement defect was found.

## New nodes

`def-sfb-weighted-additive-extension-datum` introduces the missing central additive
fppf extension with natural integer-weight torus action. Its module also gives the
actual additive global-sections functor and scalar weight formula. It uses the
existing scheme, topology, group-object and functor APIs, and supplies no theorem or
chosen object. The definition follows exactly the data in Conrad's commutator argument
and Lemma 4.3.2, printed pp.127–128. Its searches above found no existing node or
existing complete declaration of this datum. The new node cites def-pc-scheme and is
added to the item's statement dependencies; its blueprint provenance follows the
item's ancestor/via chain.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
