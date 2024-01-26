import Game.Metadata

World "ThreevenThrodd"
Level 1

Title "First Steps"

def threeven (a : Nat) := ∃ n : Nat, a = 3 * n
def throver (a : Nat) := ∃ n : Nat, a = 3 * n + 1
def thrunder (a : Nat) := ∃ n : Nat, a = 3 * n + 2

/-- Zero is threeven. --/
TheoremDoc zero_threeven as "zero_threeven" in "Threeven/Throdd"


Introduction "Just like before, we'll start with zero. Try to replicate your earlier proof
that zero is even to show that it's also threeven."

Statement zero_threeven : (threeven 0) := by
  use 0

Conclusion "Awesome!"

/- Use these commands to add items to the game's inventory. -/



-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

/-- threeven (a : Nat) := ∃ n : Nat, a = 3 * n

Divisible by three --/
DefinitionDoc threeven as "threeven"

/-- throver (a : Nat) := ∃ n : Nat, a = 3 * n + 1

One more than a multiple of three --/
DefinitionDoc throver as "throver"

/-- def thrunder (a : Nat) := ∃ n : Nat, a = 3 * n + 2

Two more than a multiple of three --/
DefinitionDoc thrunder as "thrunder"

NewDefinition threeven throver thrunder
