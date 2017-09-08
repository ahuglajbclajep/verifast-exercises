CC = ccomp
CFLAGS = -O2
LDFLAGS =
LIBS =
INCLUDE = -I$(SRC_DIR)

VFFLAGS = -disable_overflow_check

APP_NAME = Root-Finding
SRC_DIR = src
OBJ_DIR = build
SRC = $(shell ls $(SRC_DIR)/*.c)
OBJ = $(SRC:$(SRC_DIR)/%.c=$(OBJ_DIR)/%.o)

$(OBJ_DIR)/$(APP_NAME): $(OBJ)
	$(CC) -o $@ $^ $(LDFLAGS) $(LIBS)

all: clean $(OBJ_DIR)/$(APP_NAME)

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c
	@verifast -c $(VFFLAGS) $<
	@mkdir -p $(OBJ_DIR)
	@$(CC) -MM -MP -MT $@ -MF $(@:.o=.d) $<
	$(CC) -c $(CFLAGS) $(INCLUDE) -o $@ $<

run:
	@make
	@cd $(OBJ_DIR) && ./$(APP_NAME)

verif: $(OBJ)

clean:
	$(RM) $(OBJ) $(OBJ:.o=.d) $(OBJ_DIR)/$(APP_NAME)

-include $(OBJ:.o=.d)

.PHONY: all run verif clean
