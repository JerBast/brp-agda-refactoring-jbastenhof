# Correct-by-construction refactoring of functional code

![Agda](https://img.shields.io/badge/Agda-2.6.3-blue.svg?labelColor=white&logo=data:image/png;base64,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)

This repository contains a correct-by-construction approach for refactoring tuples to records in a Haskell-**like** language (HLL). This is done for the 2022/2023 edition of the BSc Research Project at the Delft Univesity of Technology. An example of the refactoring operation is shown below.

```haskell
-- Before
lastName :: (String, String, Int) -> String
lastName (_, s, _) = s

-- After
data Person = Person { initials :: String
                     , lastName :: String
                     , age :: Int
                     }
```

---

## Folder structure

All relevant information can be found in the [src](./src/) folder. The structure is as follows:

- [HLL](./src/HLL/) - Intrinsically-typed specification of the HLL and big-step semantics.
- [Proofs](./src/Proofs/) - Proof that the refactoring operation replaces all tuples by record instances and a relation between values of a pre-refactored and refactored expression.
- [Refactoring](./src/Refactoring/) - Refactoring operation that replaces all tuples by record instances. Treats all tuples as if they were unique. The accompanying record declaration is based on the type signature of the tuple.
- [Utils](./src/Utils/) - Utility folder that contains a construct which specifies that some element is in a list.
