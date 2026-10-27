## Worker report

Q05, stage 2, repair of returned immutable head b07b1ff51f52, 2026-10-25.

### Latest return H7 and H2/H1

Restored the item's base proof_deps verbatim: exactly 17 entries. Removed the
unused lem-trf-prelog-pushout-log-axiom proof edge. No statement_change is
needed because the statement and proof plan are unchanged. Dropped the sandbox
PrelogPushoutLogAxiom.lean and its theorem-node JSON, so this delivery neither
attaches nor changes that unrelated theorem's Lean record on main.

The accepted item module and PrelogUnitPushoutPresentation.lean are byte-identical
to the returned delivery; their SHA-256 digests are respectively
a1cead6c97b6938ab59f25c8211fe7bb2553de06b54478d4aae477958b656d37 and
1912164910dafcfef8ac230776b1b56ba394d9d6cc76ead489eaa105e76ad054.
The item's stmt_deps is unchanged from the returned delivery. Rebased the
existing definition node's non-Lean metadata to current main, retaining its
accepted Lean binding. Only the item and its definition dependency are delivered.

The mathematical signatures of the two item statements are unchanged. The repair
separates the definition interface from the log-axiom theorem and explicitly
compares the presentation interface that Q28 landed in the meantime. Definitions
contain actual data; every theorem proof remains `sorry`. No source statement
changes, hypotheses, or conclusions are introduced into the item.

### Return H2: definition ownership and statement dependencies

Created `def-trf-prelog-unit-pushout-presentation`, with module
`Sheaf.AlgebraicGeometry.PrelogUnitPushoutPresentation`. This is the single DAG
owner of the explicit quotient presheaf and its construction helpers. Moved all
of the following from the returned theorem modules into this definition module:
`prelogPresentationCon`, `prelogPairRestriction`, `prelogPresentationMap`,
`prelogPresentation`, `prelogPresentationPair`,
`IsPrelogPresentationSheafification`, `prelogPresentationIota`,
`prelogPresentationUnits`, their named well-definedness/functoriality/naturality
lemmas, `prelogStalkDiagram`, `prelogStalkColimits`, `prelogStalk`,
`prelogStalkMap`, `prelogSectionUnit`, and `HasPrelogUniversalMapping`.
Their docstrings now carry the new definition node's blueprint ID.

The item imports this definition module publicly. It no longer imports
`PrelogPushoutLogAxiom`, and its stmt_deps no longer contains the theorem node
`lem-trf-prelog-pushout-log-axiom`. Instead it cites the definition node.
The accepted `lem-weil-pbc-etale-site-localization-open` statement dependency
is retained, with its recorded `overEquiv` declaration used in clause (1).

The log-axiom theorem's independent module and record on current main are
outside this delivery. No item proof step uses its conclusion, and the item
imports only the definition module for presentation data.

### Return H4: Q28 interface reused and compared

Read the full current-main Q28 module
`Sheaf.AlgebraicGeometry.ZariskiPrelogLogificationComparison`, its node and
recorded declarations, then fetched its current server source using the
prescribed `scompile.py --source` reader. It defines the general-site
`PrelogPushoutPresentation`, `PrelogPairNatural`, and `prelogPairClass`, plus
`PrelogPushoutPresentation.Restricts` and `.EtaleUniversal`. These are the
same underlying notion and must not be copied.

The new definition module publicly imports that existing module and reuses its
EXACT `PrelogPushoutPresentation` structure. None of those five declarations is
redeclared or replaced. The explicit functor `prelogPresentation` is necessary
construction data absent from Q28's pair-map encoding: Q28 specifies maps out
of each objectwise quotient, while the item explicitly compares the two actual
quotient PRESHEAVES, including restriction maps. Constructing that functor is
not another definition of a bundled sheafified presentation.

The normalized comparison is now part of the definition interface:

* `prelogBundledUnit q` is constructed from q's actual pair maps. Its naturality
  lemma checks those maps against the explicit quotient restrictions, on pair
  representatives using q.naturality. No new pair map is chosen.
* `prelogPresentation_bundled_comparison` says, on the SAME underlying prelog
  sheaf and SAME structural map with the stated pair formula, that the supplied
  unit has the sheafification property iff there is a Q28 presentation whose
  induced unit is exactly that η and whose iota is exactly η([m,1]). This
  compares the encodings with their maps, not just abstract existence of
  isomorphic objects.
* `prelogUniversalMapping_bundled_iff` identifies the general-presheaf mapping
  predicate with the EXISTING `q.EtaleUniversal P L` when its domain is a prelog
  sheaf. The general predicate is needed because this item's M need not be a
  sheaf. No alternative `EtaleUniversal` is introduced.
* The existing `.Restricts` definition is reused: it means a presentation on
  every slice with exactly the original pair maps and inclusion. The item
  retains its explicit normalized equivalence for the small étale site. It
  does not introduce a competing bundled restriction predicate.

Thus the new definition node owns this explicit realization and comparison,
using Q28's bundled notion as the existing presentation notion. Q28's landed
module and theorem are not altered, and no duplicate declarations are created.
This takes the return's “justify and compare” option.

### Hypothesis-by-hypothesis and clause-by-clause rendering of the item

Both statements bind `X : Scheme.{u}` and `[IsLocallyNoetherian X]`.
`M : X.Etaleᵒᵖ ⥤ CommMonCat.{u}` is the arbitrary commutative-monoid presheaf;
`γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat` is its
natural structural homomorphism. No sheaf condition or constant-chart assumption
is placed on M. `X.etaleStructurePresheaf` evaluates as `Γ(W.left, ⊤)`.

`prelogPresentationCon γ W` reuses the recorded
`divisorialChartCongruence (γ.app (op W)).hom.mrangeRestrict`. Its generators
are `(e,1)~(1,a)` when γ(e)=a.val. Multiplying by `(m,u)` gives the node's
`(me,u)~(m,γ(e)u)`; conversely those relations with `(m,u)=(1,1)` recover the
generators. No cancellation or injectivity is needed. `prelogPresentationPair`
is the actual quotient map. Q28's `prelogPairClass` is definitionally its
value on `(m,a)`, with the same quotient object.

`prelogPresentation` constructs that quotient at every object; its restrictions
are the lift of `(M.map f.op).hom.prodMap (Units.map f.left.appTop.hom.toMonoidHom)`.
The well-definedness, identity and composition fields refer to the named
construction lemmas, never a sorry datum.

`L : EtaleLogStructure X`, `η : prelogPresentation γ ⟶ L.monoidSheaf.obj`, and
`hη : IsPrelogPresentationSheafification ...` bind the specified log structure,
specified unit, and its monoid-sheafification property. The predicate is the
hom-set bijection of the recorded Mathlib sheafification adjunction; Q28's
same predicate is compared with fixed unit as explained above. `hα` is exactly
α_L(η([m,a]))=γ(m)a at every object and pair. The explicit `@id Γ(W.left, ⊤)`
only resolves the actual section-ring type and changes no value or universe.

Clause (1), `etaleLogPresentation_restriction`:

* `U : X.Etale` is any étale U→X. The first conjunct concludes
  `IsLocallyNoetherian U.left`.
* `Scheme.Etale.overEquiv U` is the EXISTING constructed equivalence
  `Over U ≌ U.left.Etale`. The covering-sieve equivalence in the conclusion
  asserts exactly the same covers under this equivalence; the recorded
  covering-family criterion translates this to covering families.
* `prelogRestrictionFunctor U = etaleToOver U ⋙ Over.forget U` is composition
  to X. `prelogRestrictionGamma` is whiskering γ; its target is literally the
  structure presheaf on U because the test scheme and section ring are identical.
* The next conclusion is EQUALITY of the two explicit quotient presheaves
  `prelogPresentation (prelogRestrictionGamma γ U)` and the restriction of
  `prelogPresentation γ`. Equality includes restrictions and the same relations.
* `LU : EtalePrelogStructure U.left` and ηU bind the sheafification with its
  induced structural map. The two following premises are its sheafification
  property and the exact pair structural formula. LU is a prelog structure so
  that the log axiom is not assumed as a premise.
* The conclusion `∃ LLU, LLU.toEtalePrelogStructure = LU` makes THIS prelog
  structure into a log structure, with its exact sheaf and structural map.
* `∃! e : LU.monoidSheaf.obj ≅ restriction(L.monoidSheaf.obj), ...` gives the
  unique normalized monoid-sheaf comparison. The target is the actual restricted
  sheaf; a natural monoid-presheaf isomorphism between sheaves is a sheaf iso.
  The first condition fixes e on every ηU([m,a]), hence eηU=η|_U. The next
  condition is structural compatibility on EVERY section. The last two conditions
  explicitly preserve the maps m↦η([m,1]) and a↦η([1,a]).

Clause (2), `etaleLogPresentation_comparison`:

* `K : EtaleLogStructure X`, `v : M ⟶ K.monoidSheaf.obj`, and
  `hv : v ≫ K.alpha = γ` are precisely the second log structure and its
  compatible natural homomorphism.
* The actual given map `f : L.monoidSheaf ⟶ K.monoidSheaf` is retained, with
  BOTH `hf : f.hom ≫ K.alpha = L.alpha` and the exact sectionwise `hpair`
  formula fη([m,a])=v(m)j_K(a).
* `prelogSectionUnit K W a` is the inverse of the structural units map, followed
  by inclusion of monoid units, as in the recorded stalk unitsIn. The log axiom
  makes that units map sectionwise bijective (local unique lifts glue). Thus
  it is the TRUE inverse, not an arbitrary chosen map.
* `prelogStalkDiagram M t` is exactly the opposite pointed-neighbourhood
  diagram used by `pointedEtaleStalkDiagram`, without assuming M is a sheaf.
  Its actual monoid colimit `prelogStalk M t` is supplied using the explicit
  filtered colimit on a small final model. `prelogStalkMap` is `colim.map`
  of the whiskered natural transformation and lands in the existing
  `pointedEtaleStalk` of the target monoid sheaf.
* `hstalk` quantifies over every Ω : Type u, Field Ω, IsAlgClosed Ω, and
  t : Spec(.of Ω)→X, exactly the recorded geometric-point convention. Its two
  `IsStalkChart` assertions are on the CANONICAL maps induced by i and v.
  The recorded definition is surjectivity of the product-with-units map and
  equality of its kernel with the generated pushout congruence. This is exactly
  each displayed canonical map Q_t→L_t or Q_t→K_t being an isomorphism.
  The compatibility assumptions identify their structural composites with
  the same induced γ_t, so no different source Q is substituted.
* The conclusion gives e : L.monoidSheaf ≅ K.monoidSheaf with e.hom=f and
  the inverse's explicit structural compatibility. It proves that THE GIVEN
  f is an isomorphism of log structures.
* `HasPrelogUniversalMapping` is injectivity of precomposition on the actual
  subtype of maps commuting with α, with range EXACTLY the compatible maps
  M→N, for EVERY log structure N. The implication transfers that bijection
  from L and i to K and v. It adds no chart or sheaf assumption on M.

### Dependency declarations used

`Mathlib.AlgebraicGeometry.Noetherian`: IsLocallyNoetherian and
LocallyOfFiniteType.isLocallyNoetherian. `...Sites.Etale` and
`...Morphisms.Etale`: Scheme.smallEtaleTopology, Scheme.Etale, Etale and the
jointly-surjective covering-family criterion. `Mathlib...Sheafification` and
`PreservesSheafification`: sheafificationAdjunction, sheafifyComposeIso,
sheafComposeIso_hom_fac. Their full recorded signatures/docstrings were read.

`Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: EtalePrelogStructure,
EtaleLogStructure, stalk, unitsIn and IsStalkChart. Its recorded LogRegularPair
import supplies divisorialChartCongruence, divisorialChartPushout and
strictLocalRing. `Sheaf.AlgebraicGeometry.PointedEtaleStalk` supplies the
existing pointedEtaleStalkDiagram, pointedEtaleStalk and filtered-colimit model.
`Mathlib.FieldTheory.IsAlgClosed.Basic` and `AlgebraicGeometry.ResidueField`
supply IsAlgClosed and the recorded inline geometric-point convention.
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver` supplies overEquiv,
etaleToOver and its covering compatibility. Q28's exact definitions and the
new shared construction/comparison module are specified above.

Available proof-dependency modules are retained as plain imports: finite
presentation/type and affine local-property criteria, CoverLifting for the
set-valued slice sheafification, filtered set colimits, conservative points and
algebraic closures. The genuinely unstated proof-only
`lem-trf-filtered-ring-log-pushout` has no module; its specific representative
argument remains in the proof docstring. The item does NOT need the log-axiom
theorem's conclusion merely to state its presentation data.

### Edge cases, source checks and searches

Checked X empty, U empty and U=identity, a non-sheaf M with nontrivial empty
sections, nonconstant transition maps, noncancellative monoids, noninjective γ,
the trivial monoid, zero section rings and nontrivial units. Every quotient is
the actual congruence quotient. No fine/saturated/integral or nonempty hypothesis
is added. Empty X gives vacuous geometric-point tests consistently with terminal
sheaf categories. The site has object universe u+1 and morphism universe u; the
small final model provides monoid colimits in u. No equality of site universes
or vacuous smaller universe of tests is imposed. Compared encodings on the same
underlying quotient: the empty object and non-sheaf case are included in Q28's
general presheaf parameter, not a specialization to prelog SHEAVES.

Read ILO VI 1.1 printed p.69 (PDF p.75), the Stacks Tag 00YR sheafification APIs,
and the item/prerequisite node statements and proofs. The detailed comparison
is the node's expressly agent-written argument; Kato (1988) is not claimed read.
Read Q28's server source and current main. The current return accepts the
mathematical signatures. This repair changes no Lean file and only restores
the correct delivery scope and base proof dependencies.

New searches actually run and recorded in the new node from searches.jsonl:
LeanSearch “A prelog monoid presheaf with a map to a ring presheaf has a unit
pushout presentation whose sheafification has a universal property” returned
8 generic/module-sheafification results. LeanFinder “Commutative monoid prelog
unit pushout quotient presheaf and sheafification presentation” returned
8 module presentation results. Mathlib grep
`PrelogPushoutPresentation|prelogPresentation|prelogPairClass|prelog|LogStructure`
in AlgebraicGeometry returned zero hits. Direct rg of lean/WeilConjectures
returned no corresponding notion; lean/Sheaf located Q28's exact declarations,
which are REUSED. The initial DAG search located its theorem node but no definition node
owning the explicit presheaf realization. During the repair, current main
acquired the definition node specified here; its content agrees with the
sandbox exactly apart from the Lean binding supplied in this delivery. `blueprint_refs.py search prelog`
returned zero matches; ancestor is lem-trf-local-term-locality. The new node
records all query results as they ran, including the positive project match.
Earlier item searches remain valid and are retained in searches.jsonl.

## New nodes

`def-trf-prelog-unit-pushout-presentation` owns the explicit quotient presheaf,
its canonical maps and geometric-stalk helpers, the universal-map predicate,
and the normalized comparison with Q28's EXISTING bundled presentation. Its
source is ILO VI 1.1 and Stacks Tag 00YR; the explicit characterization of the
two encodings is agent-written. No new bundled presentation is defined.
Q28 gives pair-map/universal-property data, while the explicit functor and its
restriction/composition data are absent there and necessary for P_U=P|_U.
The shared module imports and uses Q28's actual structure, its pair naturality
predicate and its universal mapping predicate. The comparison fixes the unit
and inclusion exactly. Searches, source, blueprint ancestry, creation metadata,
empty proof fields, import_flags and the lean record follow brief-stage2 §5.
The definition node is cited directly by the item and by the log-axiom prerequisite.
It now exists on current main without Lean; this delivery attaches its module.
Each named construction/normalization theorem is a clause of this definition
node's explicit characterization, with source and natural-language proof.

## Dependency modules

The existing def-trf-prelog-unit-pushout-presentation node receives the accepted
PrelogUnitPushoutPresentation module. The log-axiom theorem module and node
record are omitted as instructed by the latest return.

## Second reading by Q05

Self-audit only; the maintainer supplies independent review. H7: the item has
exactly the 17 base proof dependencies. H2/H1: the unrelated theorem's sandbox
module and node record are absent. The accepted two modules have the digests
listed above, and the item stmt_deps remains unchanged. The item imports the
definition module, whose normalized Q28 comparison remains intact. All
mathematical clauses and edge cases approved in the return are preserved.
