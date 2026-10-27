# Reuse the existing internal Hom section component lemma

## Reason

The return of delivery 40fc7aa56 refuses a duplicate private theorem in
LocalRHomCanonicalNaturality. The existing theorem is private in
HomComplexSectionsHomotopyNaturalityOfUniverses, so importing its module alone
cannot expose it. Make that existing theorem public and import and reuse it.

## Old and new

In Sheaf.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses,
change `private lemma homObjMap_section_component` to
`lemma homObjMap_section_component`, adding a docstring. Its explicit binders,
statement and `rfl` proof stay verbatim. All other declarations and imports stay
verbatim. The module is unclaimed (no claim file at repair time).

In the new LocalRHomCanonicalNaturality module, remove the duplicate helper and
replace its private HomComplexProjections import by a private import of the
existing HomComplexSectionsHomotopyNaturalityOfUniverses module. The existing
rewrite now uses the imported public lemma. The main naturality statement and
proof are otherwise unchanged.

## Consumers

The downstream tool reports 3514 transitive modules. Its declaration-use check
finds only HomComplexSectionsHomotopyNaturalityOfUniverses itself (the declaration
and its rewrite). The only direct current Lean importer is
HomComplexSectionsDerivedNaturalityOfUniverses. Its theorem signatures and proofs
need no adaptation: the same local rewrite still resolves to the same statement.
The new consumer is LocalRHomCanonicalNaturality in this delivery. Exposing a
proved theorem changes no definition or instance; no target changes meaning.
No adopted source-library module is changed.

## Status

Open pending the independent review and global build. The complete eleven-module sandbox passed lcompile.py --all
(result 4077ae6c1e967b30d8c2091b); the delivery gate performs its checks.
